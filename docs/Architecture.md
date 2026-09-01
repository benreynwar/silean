# Silean architecture

Silean describes a hardware hierarchy, gives that hierarchy an
order-independent meaning, and proves that the meaning satisfies separately
written behavioral contracts. The same hierarchy is traversed directly when
emitting FIRRTL; there is no lowered circuit representation in between.

This document describes the current design. [SourceMap.md](SourceMap.md) maps
the concepts to files, and [../Roadmap.md](../Roadmap.md) lists only future
work.

## Correctness boundary

The formal chain is:

```text
typed ModuleStructure
        |
        v
simultaneous structural equations
        |
        v
exact cycle contract
        |
        +--> reset-synchronized trace contract
        |
        +--> latency-independent FIFO contract
```

Lean checks this chain through the abstract FIFO behavior. It does not yet
prove that FIRRTL rendering, CIRCT lowering, or SystemVerilog simulation
preserves the structural equations. Generated hardware is covered by an
end-to-end regression, not by a backend-correctness theorem.

## Typed signals and boundaries

`SignalType` is recursive:

- `.bit` denotes `Bool`;
- `.vector length element` denotes `Fin length -> element.Denote`; and
- `.tuple fields` denotes a dependent nested product.

`SignalMap` adds finite symbolic labels to signal types. `ModulePorts` contains
one labelled input map and one labelled output map. Labels are part of the
types used by wiring, so a connection identifies ports by name and can only
connect equal signal shapes.

`Enumeration`, `ListIndex`, `DependentList`, and `EnumeratedMap` provide finite
typed lookup. They retain the evidence needed to index heterogeneous maps
without converting module code to untyped numeric positions.

## Structural hardware

A `ModuleBody` is one uninstantiated hierarchy layer. It owns:

- the parent ports;
- the labelled boundaries of every child instance; and
- total wiring for every parent output and child input.

Every sink has exactly one same-typed source. Reusing a source gives fan-out.
Undriven sinks and shape-mismatched connections cannot be constructed.

`ModuleStructure` completes the hierarchy by choosing one of five forms:

- a `Primitive` leaf with output and next-state equations;
- an explicit `blackbox` leaf whose equations are assumed;
- a lossless aggregate `splitter`;
- a lossless aggregate `combiner`; or
- a `composite` body with a complete structure for each child.

Splitters and combiners are structural leaves rather than programmable
primitives. Their low-level shapes and inverse value operations live in
`Composition.SignalAdapter` because `ModuleStructure` must mention them.
Their equations and cycle certificates live later in
`SignalAdapterImplementation`.

A structure contains no contract, schedule, evaluator, emitted name, or
backend metadata. Its state is derived recursively from primitive-local state;
a stateless hierarchy therefore has zero state labels rather than a separate
stateless representation.

`ModuleStructure.HasNoBlackboxes` recursively states that the complete
hierarchy has no opaque leaves. `hasNoBlackboxes` is its executable Boolean
check, with a proof that the Boolean and proposition agree. Closed FIRRTL entry
points require this evidence.

## Order-independent structural meaning

`ProposedValues` assigns boundary outputs and primitive next-state values at
every occurrence in a hierarchy. Given current inputs and state,
`ModuleStructure.IsSolution` requires:

- every primitive or adapter equation to hold;
- every child proposal to solve that child's equations with its wired inputs;
  and
- every parent output to equal its wired source.

This is a relation over simultaneous equations, not an evaluation algorithm.
A proof schedule can demonstrate that a solution exists and is unique, but
the schedule does not define what the circuit means. This distinction prevents
an arbitrary evaluation order from assigning meaning to unsupported
combinational feedback.

`ModuleStructure.Transition` and `Executes` chain the same relation over clock
cycles. They remain independent of behavioral contracts.

## Exact cycle contracts

`ModuleCycleContract` gives natural one-cycle behavior using its own labelled
state. It contains named output rules and one next-state rule. Each output rule
declares the exact inputs it reads and outputs it writes. The contract state
need not have the same shape as the structural state.

`ModuleCycleCertification structure contract` contains:

1. a relation between contract state and structural state;
2. proof that every structural state has a corresponding contract state;
3. existence of a structural solution for every input and state;
4. uniqueness of that solution; and
5. proof that every structural solution obeys the contract and preserves the
   state relation.

Quantifying over every solution keeps correctness independent of the schedule
used to prove existence and uniqueness.

`ModuleCycleCertified` bundles a concrete structure, contract, and
certification for public use. `ModuleCycleCertifiedLayer` instead certifies an
uninstantiated `ModuleBody`: for every family of children satisfying declared
child contracts, the resulting parent structure satisfies its parent
contract. This prevents parent proofs from depending on child internals.

### Proof schedules

An output schedule calls the public child rules needed to establish one parent
output rule. A state schedule calls the rules needed to supply every child's
explicit next-state inputs and state result. `RuleSchedules.CoversChildren`
requires the combined schedules to exercise every immediate child rule.

The generic construction proves:

- scheduled reads are available before each call;
- complete coverage gives at most one structural solution;
- replaying the schedules with certified children constructs a solution; and
- child solutions expose their public contract facts to the parent proof.

`RuleSchedules.certifiedLayer` packages those generic existence and uniqueness
results with the module-specific state correspondence and `Implements` proof.
Recursive module families use the same constructor at each base and
successor/node layer; recursion only chooses the already-certified recursive
child.

## Worked composite: HalfAdder

`Modules.HalfAdder` is the smallest complete example of the intended pattern.
Its public boundary has two bit inputs, `left` and `right`, and two bit outputs,
`sum` and `carry`. Its natural contract says:

```text
sum   = left XOR right
carry = left AND right
```

The structure has two named children:

```text
halfAdder
|- sumGate   : XOR primitive
`- carryGate : AND primitive
```

Both children read the parent inputs. The parent outputs are wired directly to
their corresponding child outputs. The body mentions only the XOR and AND
boundary contracts, not their structures.

There is one parent output rule and schedule for each independent result. The
sum schedule calls only the XOR rule; the carry schedule calls only the AND
rule. Their union covers both child rules. Generic schedule theorems establish
existence and uniqueness for any certified implementations of those child
contracts.

The remaining `implements` proof applies each child's public contract fact and
uses the two boundary wiring equalities. `certifiedLayer` therefore proves the
wiring correct without unfolding either primitive implementation. Concrete
XOR and AND structures are supplied afterward to obtain the public closed
`HalfAdder.certified` value. `FullAdder` then uses the HalfAdder contract in
exactly the same way rather than inspecting its gates.

## More abstract contracts

Exact cycle contracts are deliberately not the only specification form.

### Reset contracts

`ModuleResetContract` describes finite traces after a synchronous reset. Its
specification state may be any Lean type and has no public mapping to structural
state. Behavior before reset is unconstrained. After reset, expected output
bits may be zero, one, or `dontCare`.

The corresponding certificate still requires structural execution to exist,
so an inconsistent circuit cannot satisfy the contract vacuously.

### FIFO contracts

`FifoContract` observes valid/ready transfers rather than fixed output
latency. Before the first reset it imposes no behavior. Reset synchronizes an
empty bounded logical queue. Each ordinary cycle requires:

```text
old queue ++ accepted inputs = produced outputs ++ new queue
```

This permits both fall-through and registered FIFOs while guaranteeing order,
no invented output payloads, and bounded capacity. Over a reset-free suffix,
produced payloads are a prefix of accepted payloads; they are equal when the
final queue is empty.

The pointer FIFO is first certified against an exact cycle contract. A private
`FifoCycleRefinement` relates its pointer/register-bank state to a logical
queue and proves reset establishment, invariant preservation, capacity, and
the transfer equation. `Modules.Fifo.fifoCertified` exposes only the structure
and standard FIFO contract.

Lean reports these axioms for that public certificate and its structure and
contract projection theorems:

```text
propext, Classical.choice, Quot.sound
```

They are Lean's standard logical/quotient axioms. The result depends on no
project-defined axiom, `sorry`, `admit`, or unsafe definition.

## Naming and FIRRTL

`ModuleNaming` is indexed by an exact `ModuleStructure`. It supplies stable
definition keys, port names, instance names, and recursive child naming without
being stored in the hardware structure. Generic naming traversals live under
`Naming/`; module-specific naming normally lives beside its module.

The FIRRTL renderer traverses `ModuleStructure` directly. It supports
primitives, adapters, blackboxes, and composites, validates names and
definitions, and emits FIRRTL 4 text. Configured executable emitters live in
`Emitters/`. The Nix regression lowers FIRRTL with CIRCT, compiles with
Verilator, and tests with cocotb.

This backend path is executable evidence only. A semantics-preservation proof
from structural equations to FIRRTL remains future work.

## Deliberate limits

- Signals are two-state; `X`, `Z`, analogue behavior, timing, metastability,
  and clock-domain crossings are not modeled.
- There is one implicit global clock. Reset behavior is represented explicitly
  in ports and contracts.
- Blackboxes are explicit assumptions. Closedness proves their absence but
  does not prove the FIRRTL backend.
- Schedules are proof witnesses, not synthesis directives or stored hardware.
- High-level correctness depends on the chosen contract. Exact cycle, reset,
  and FIFO contracts express different observable guarantees.

## Dependency direction

The intended source direction is:

```text
Foundation
  -> low-level adapter shapes / Structure
  -> Semantics and Contracts
  -> generic Composition and adapter certification
  -> concrete Modules
  -> Naming and FIRRTL
```

Generic Composition imports neither concrete Modules nor Naming. Tests and
configured emitters sit above the reusable library.
