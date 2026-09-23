# Silean architecture

Silean is an embedded structural hardware language and verification framework
in Lean. A design is an ordinary typed Lean value describing ports, child
instances, wiring, primitive equations, and state. Independent Lean
specifications describe what that hardware should do.

The central architectural decision is to keep three concerns separate:

1. **Structural meaning:** which simultaneous equations define the hardware?
2. **Executability:** do those equations have one result for every input and
   current state?
3. **Behavioral correctness:** does that result satisfy the natural property
   expected at the module boundary?

They are related by proofs, but none is defined in terms of the others. This
lets a module use an exact cycle contract, a fixed-latency function, a framed
packet relation, or a custom observational theorem without changing what its
hardware structure means.

This document explains that model. [SourceMap.md](SourceMap.md) maps concepts
to files, [ModuleOrganization.md](ModuleOrganization.md) gives conventions for
individual modules, and the project-wide [roadmap](../../Roadmap.md) records
current and future work.

## The overall picture

For a concrete design, the main relationships are:

```text
authoring
    |
    v
ModuleStructure ----> simultaneous equations ----> execution
    |                         |
    |                         +---- structural rules
    |                                      |
    |                                      v
    |                              existence / uniqueness
    |
    +---- refinement proof ----> natural behavioral contract
```

For a top-down design whose children are not implemented yet:

```text
ModuleBody + synchronized child traces + wiring
                         |
                         | child predicates
                         v
                 parent trace predicate

concrete composite execution
            |
            +---- generic projection ----> the same ModuleBody trace
```

The second path is not an executable blackbox semantics. It is an ordinary
conditional theorem about interfaces and wiring. Once concrete children are
supplied, their execution discharges those same child predicates.

## Typed boundaries

`SignalType` describes recursively shaped values:

- `.bit` denotes `Bool`;
- `.vector length element` denotes `Fin length → element.Denote`; and
- `.tuple fields` denotes a dependently typed collection of named fields.

`SignalMap` adds finite typed labels, and `ModulePorts` pairs an input map with
an output map. Labels and signal shapes occur in the types of endpoints and
wiring, so a child input cannot accidentally be connected to an unrelated or
differently shaped signal.

Most module boundaries are declared with `module_ports`:

```lean
module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  output result : .vector width .bit
```

The command generates the input and output label types, their `SignalMap`s,
the resulting `ModulePorts`, emission naming, and typed helpers for authoring
and child placement. It only describes the boundary; it does not attach
behavior or implementation.

`signal_schema` provides the corresponding convenience for reusable named
aggregate signals. It generates the tuple shape, typed field labels and
accessors, and naming schema together. The underlying structural signal type
remains independent of those emitted field names.

These commands are boilerplate generators, not a second language with a
different meaning. Their products are ordinary Lean definitions. Generated or
recursive families can use ordinary Lean directly when that is clearer.

## Bodies and concrete structures

A `ModuleBody` is one permanent hierarchy layer. It contains:

- the parent boundary;
- the typed boundary of every immediate child; and
- one same-shaped source for every parent output and child input.

Every sink therefore has exactly one driver. Reusing a source gives fan-out,
while undriven sinks and shape mismatches are excluded by construction.

A `ModuleStructure` chooses an implementation recursively. It has four forms:

- a `Primitive` with output and next-state equations;
- a lossless aggregate splitter;
- a lossless aggregate combiner; or
- a composite `ModuleBody` with one concrete `ModuleStructure` for each child.

Structural state is derived from the primitive-local state throughout that
tree. A stateless hierarchy simply has no state labels.

`module_design` is the main command for writing a composite. In one declaration
it combines either a new or reused boundary, fixed or indexed child families,
optional named wires, and typed wiring:

```lean
module_design HalfAdder where
  boundary (HalfAdder.ports) (naming := HalfAdder.Naming.ports)
  instances {
    sumGate := Primitives.xorDesign,
    carryGate := Primitives.andDesign }
  wiring {
    outputs {
      .sum := sumGate.output,
      .carry := carryGate.output }
    instance (.sumGate) {
      .left := input.left,
      .right := input.right }
    instance (.carryGate) {
      .left := input.left,
      .right := input.right }
  }
```

The command always generates the child interfaces, wiring, and `body`. When
every child is concrete, it also generates `moduleStructure`, recursive
naming, and the final named `design`.

A child may instead be written as `unresolved (ports)`. It then contributes
only its typed interface to the body. Replacing that expression with a
concrete child design leaves the boundary and wiring unchanged and causes the
same declaration to become executable. There is no fake state, transition
relation, or unconstrained solution for an unresolved child.

## Simultaneous structural meaning

One `HierStep` contains parent boundary values, the corresponding assignment
for every child recursively, and current and next structural state.
`ModuleStructure.IsSolution` says that:

- every primitive, splitter, and combiner equation holds;
- every child assignment solves the child's equations;
- every child input equals its parent-wired source; and
- every parent output equals its wired source.

This is a relation over simultaneous equations, not an evaluation algorithm.
Storage feedback is meaningful because current and next state are distinct.
Unsupported combinational cycles do not acquire an accidental meaning from a
chosen evaluation order.

`Transition` and `Executes` chain the same relation across cycles. Observation
then erases internal state and hierarchy to ordinary boundary steps and traces.

## Existence and uniqueness

Behavioral correctness alone is insufficient: an inconsistent circuit could
satisfy a theorem vacuously, while an ambiguous combinational network could
have several results. Silean therefore proves structural existence and
uniqueness independently of the chosen behavioral contract.

`ModuleStructuralRules` describe only which boundary inputs are needed to
produce which outputs and next state. A complete, dependency-correct schedule
over certified children constructs a solution and proves it unique.
`ModuleStructuralCertification` connects those rules to a concrete structure.

Exact cycle contracts can automatically erase to precise structural rules.
Modules with another contract style can supply rules directly, and every
structurally certified module also has a conservative whole-module rule.

The `module_complete_schedule` command is a readable way to give a
contract-independent dependency order. The elaborator checks availability and
coverage and produces the formal schedule proof. Schedules are proof witnesses:
they neither define circuit meaning nor become hardware.

## Behavioral specifications

Silean does not require one universal contract type. A public specification
should use the most natural Lean statement for the boundary.

### Exact cycle contracts

`ModuleCycleContract` is useful for local hardware whose exact one-cycle
behavior is the right abstraction. It has an independent behavioral state,
named output rules, and one complete next-state rule. Each output rule declares
the inputs it reads and outputs it determines.

`module_cycle_contract` generates the rule names, typed selections, equations,
coverage proof, and assembled contract from a readable declaration:

```lean
module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule sum where
    reads := [left, right]
    writes := { sum := sumValue left right }
  output_rule carry where
    reads := [left, right]
    writes := { carry := carryValue left right }
  state_rule where
    reads := []
    next := {}
```

The generated equations form the public child interface used by parent proofs.
The contract does not mention the child's gates or register layout.

### State-free temporal contracts

`BoundaryTrace` is a finite sequence of boundary input/output observations. It
contains no structural or behavioral state.

`FixedLatency` relates every available output to an earlier input through an
ordinary Lean function. `FramedLatency` relates complete marked input and
output frames after a fixed latency. An early marker invalidates the interrupted
candidate frame and may begin a later valid one.

These forms describe pipelined arithmetic and streamed FFT modules more
naturally than reproducing their register chains as contract state.

### Other contracts

Reset-synchronized contracts constrain behavior only after reset and may use
ternary output expectations. FIFO contracts observe accepted and produced
valid/ready transfers through an abstract bounded queue, without fixing the
implementation latency.

Nothing prevents a module from using a custom predicate instead. The framework
requires explicit proofs at composition boundaries, not inheritance from one
privileged contract class.

## Bottom-up composition

In bottom-up certification, every child already has a concrete structure and a
public contract or structural rule interface. The parent proof uses those
interfaces rather than unfolding the child implementation.

For exact cycle contracts, `module_rule_schedules` declares which child rules
establish each parent output and next-state result. The elaborator checks
dependency order and complete coverage. `module_cycle_certification` then
packages the structural schedules, state correspondence, and module-specific
behavioral proof.

The half adder is the smallest example. Its XOR and AND children are supplied
after the body is certified generically against their public contracts.
`FullAdder` then consumes the half-adder contract rather than inspecting its
gates. Larger recursive and generated modules use the same principle, often
with ordinary Lean definitions for the recursive family.

## Top-down composition

Top-down work starts from the same `ModuleBody` but permits unresolved child
interfaces. One `ModuleBody.Step` bundles a parent boundary observation with
one observation for every immediate child. A `ModuleBody.Trace` is a
cycle-aligned list of those steps.

`trace.WiringHolds` states that every parent output and child input agrees with
the permanent body wiring. A module-specific theorem may combine this fact with
arbitrary predicates on `trace.child childName` to prove an arbitrary predicate
on `trace.parent`. The framework does not prescribe a contract kind or collect
assumptions automatically.

When all children become concrete, a generic bridge projects
`ObservedExecutes` for the composite to the same body trace. It proves the
wiring fact and identifies each child projection with that child's observed
execution. The conditional top-down proof is therefore retained rather than
rewritten when implementation proceeds.

HTFFT uses this style. Its complete streaming boundary and stage chain were
proved first from natural framed contracts for the immediate children. The
children can now be refined independently while the parent bodies and proofs
remain fixed.

## Authoring identity, naming, and emission

Typed structural endpoints are the semantic identity of wiring.
`CircuitDescription` also preserves description-local structural IDs for
parent ports, child instances, and child ports. Reader-facing `SourceName`s are
metadata and are not used to recover endpoint identity in correctness proofs.

This matters because emitted names may be chosen, parameterized, or rejected
for collisions without changing the circuit's meaning. `ModuleNaming` is
indexed by the concrete structure and supplies definition keys, port names,
instance names, and recursive child naming for emission.

The FIRRTL renderer traverses `ModuleStructure` directly. It supports the
concrete primitive, splitter, combiner, and composite forms, validates emitted
definitions and names, and produces FIRRTL text. Configured regressions lower
that text with CIRCT and simulate generated SystemVerilog.

## Formal boundary and deliberate limits

Lean currently proves properties through `ModuleStructure` and its execution.
It does not prove that FIRRTL rendering, CIRCT lowering, or SystemVerilog
simulation preserves those equations. Backend compilation and simulation are
important regression evidence, not part of the formal theorem.

Other current limits are:

- signal values are two-state; `X`, `Z`, analogue behavior, timing,
  metastability, and clock-domain crossings are not modeled;
- one global clock is implicit, while reset is explicit and module-specific;
- unresolved children cannot be executed or emitted; and
- progress properties may require explicit environmental assumptions.

## Architectural lessons so far

- Keeping structure and natural specification separate makes both easier to
  read and reuse.
- Existence and uniqueness belong to structural semantics, not to one
  particular behavioral contract.
- Contract state should describe the behavior, not mirror the implementation's
  register tree.
- Top-down proofs need synchronized boundary traces and explicit assumptions,
  not executable blackboxes.
- Emitted names are metadata, not semantic identity.
- Macros are valuable when they remove repeated typed boilerplate, but
  recursive and unusual constructions should remain ordinary Lean.
- When a compositional proof becomes awkward, it is worth checking the
  framework boundary before adding module-specific proof machinery.
