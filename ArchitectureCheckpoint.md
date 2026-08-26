# Silean 2 current architecture

This document describes the current design. `Roadmap.md` retains chronological
goal outcomes, including descriptions of approaches that were later replaced.
`Design.md` records detailed rationale.

## Purpose

Silean 2 is testing whether a readable, typed, Verilog-like hierarchy can have
an independent mathematical meaning and be proved to implement behavioral
contracts without lowering to a second semantic netlist.

The validated path is:

```text
typed module hierarchy
  ports + child instances + total wiring + primitive storage
                  |
                  v
order-independent structural equations (`ModuleStructure.IsSolution`)
                  |
       +----------+-----------+
       |                      |
       v                      v
certified rule schedules  module cycle contract
existence + uniqueness    rules + abstract state
       |                      |
       +----------+-----------+
                  v
one-cycle refinement (`Implements`)
```

Neither schedules nor contracts define structural meaning. A schedule is
positive evidence that structural equations can be evaluated; a contract is an
independent statement of desired observable behavior.

## Structural description

- `SignalType` describes bits, vectors, and anonymous tuples.
- `SignalMap` gives a structural shape readable symbolic labels and typed
  `Values`.
- `ModulePorts` contains only module inputs and outputs.
- `Instances` maps each symbolic child name to its exact ports.
- `Wiring` gives every boundary output and child input exactly one same-typed
  source. Fan-out is ordinary source reuse; undriven sinks are unrepresentable.
- `Primitive` is an open leaf-description record containing ports, local state,
  equations, and output dependencies. The concrete primitives are single-bit,
  independent values under `Primitives/`; adding one does not modify a central
  enumeration.
- `ModuleStructure` is a primitive leaf or a composite that recursively owns one
  correctly typed child structure for every instance.
- A primitive explicitly owns local state. Composite structural state is
  derived from the child-instance hierarchy. Stateless state is the canonical
  zero-label map.

This remains close to a hardware module body. Contracts, schedules, evaluators,
emitted names, and backend metadata are not stored in `ModuleStructure`.

## Structural meaning

`ProposedValues` contains boundary outputs at every module occurrence and next
state at primitive leaves. Child inputs and composite next state are derived.

`ModuleStructure.IsSolution inputs currentState proposal` is the
order-independent meaning of one cycle. It requires primitive equations, child
equations, and boundary wiring to hold. It does not prescribe evaluation order.

`StructuralRule` is the small semantic dependency fact that selected module
inputs determine selected outputs among arbitrary satisfying proposals. Every
named rule of a `ModuleCycleCertified` child generically induces this fact.

`Certified.Schedule` is parent proof data. A call names a child and one of that
child's contract rules. It neither contains a child structural rule nor calls a
child evaluator or child schedule. One schedule is supplied for each parent
output rule and one for state. Their rule occurrences are combined with
duplicates omitted, and coverage requires every immediate child contract rule
to be exercised. The combined schedule proves
`ModuleStructure.HasAtMostOneSolution`; it is positive acyclicity evidence and
does not change the order-independent meaning.

Existence is stored propositionally as `hasStructuralResult` in the certified
child interface. Together with `structuralResultUnique`, it gives exactly one
structural result without selecting or exposing an evaluator. The
bidirectional DualNot regression constructs the parent existence proof using
only those child existence facts and the child `implements` proofs.

`ExecutableStructuralRule` and `StructuralEvaluator` have been removed. Each
useful parent uses named child contract rules for its local schedules,
certified child existence to construct a structural result, and child
refinement proofs to connect that result to behavior.

## Behavioral contracts

`ModuleCycleContract` is separate from `ModuleStructure` and owns abstract
contract state. It contains:

- output rules with precise input-read and output-write selections;
- exact, nonoverlapping coverage of every output; and
- one total next-state rule.

`CycleOutputRule.Holds` says one rule agrees with complete output values.
`ModuleCycleContract.OutputRulesHold` requires this for every rule.
`ModuleCycleContract.EvaluatesTo` adds the next-state requirement. This relational
form is useful in refinement because it can be applied directly to structural
outputs.

Contracts are already deterministic. `applyOutputRules` assembles their
disjoint writes, and `evaluate` returns the assembled outputs together with
next contract state. Typed assignment/fold machinery is private implementation
detail. Generic theorems prove that `evaluate` satisfies `EvaluatesTo` and that
any two satisfying evaluations agree. There is no separate contract solving
layer.

## Structural-to-contract refinement

`Implements moduleStructure cycleContract stateCorresponds` quantifies over
every structural proposal satisfying `ModuleStructure.IsSolution` at
corresponding current states. It requires:

1. the proposal's boundary outputs and some next contract state satisfy
   `contract.EvaluatesTo`; and
2. that next contract state corresponds to the proposal's derived next
   structural state.

The definition does not use a structural evaluator, uniqueness theorem, or
schedule. Those establish executability of a structure; refinement establishes
correctness of every structurally valid result.

Validated refinement examples are:

- BitMux: a gate hierarchy implements its one-rule bit-mux contract;
- hierarchical DualNot: two independent structural cones implement two
  independent contract rules; and
- generic EnabledRegister: a bit-valued enable selects between the current
  `T`-valued state and new `T`-valued input through generic Mux, then feeds the
  result to generic Register. Its state correspondence delegates to the
  Register certificate instead of exposing that child's recursive state tree.
- generic Register: bits use the bit-register primitive, while vectors and
  named tuples split into immediate components, recursively instantiate the
  same certified register, and combine the registered components. Aggregate
  contract state is related to the recursively owned bit-level structural
  state through the component certificates.
- generic Mask and BitwiseOr: bit cases wrap the closed AND and OR primitives;
  vector and tuple cases use splitters, a finite family of recursively certified
  components, and a combiner. Mask broadcasts one bit while BitwiseOr splits
  both aggregate operands.
- generic Mux: a shallow hierarchy composes NOT, two generic Masks, and generic
  BitwiseOr. Its refinement proof uses only the child certificates and keeps
  the mask/OR selection identity private to the module proof.

These examples demonstrate the shape later generic hierarchical refinement
composition should support, but no such automation is currently foundational.

The structural vocabulary also expresses a generic one-entry fall-through
FIFO. `FifoControl` computes bit-valued upstream readiness and the shared
storage-update condition. `OneEntryFifo T` composes `EnabledRegister .bit` for
valid state, `EnabledRegister T` for payload state, that control module, an OR
primitive, and `Mux T`. Its contract records bit-valued validity and
`T`-valued stored data with separate forward and ready output dependencies.
Its schedules and child uniqueness proofs establish a unique structural
result, while its existence and refinement proofs consume only the public
child certificates. The result is exported as `ModuleCycleCertified` for every
signal type. Direct checks cover fall-through, capture, backpressure, and
simultaneous dequeue/replacement for bit, vector, and nested tuple payloads.

## Certified cycle modules

Every reusable module exposes its `moduleStructure` directly as a computable
definition. This is the structural API consumed by hierarchy traversal,
naming, and direct FIRRTL generation; evaluating it never evaluates a proof.

`ModuleCycleCertification structure contract` contains only correctness
evidence indexed by an already chosen structure and contract: their state
correspondence, correspondence coverage, `Implements`, and order-independent
existence and uniqueness. A generic transport operation moves the complete
dependent proof across a proved structure identity, so concrete proofs do not
contain scattered casts. Module certification values are opaque/noncomputable;
they cannot accidentally become the source of emitted structure.

`ModuleCycleCertified` remains the convenient composition bundle formed from
the public structure, public contract, and indexed certification. It stores no
schedules and no evaluator. The state-coverage field prevents an always-false
relation from certifying a structure vacuously. Parent proofs use this bundle
through contract-facing operations such as `Certified.childImplements`.

BitMux, FifoControl, generic Register, Mask, BitwiseOr, Mux, EnabledRegister,
and OneEntryFifo all follow this boundary. Their public structures are
computable; their proof implementations are opaque.

## File responsibilities

- `Types`, `Primitive`, `Component`, `Endpoint`, `Structure`, `ModuleStructure`:
  structural vocabulary and ownership.
- `SignalLayout`, `SignalAdapter`, `SignalAdapterCertified`: vector/tuple
  immediate-component indexing plus the two closed, lossless structural
  components `SignalSplitter` and `SignalCombiner` and their certificates.
- `StructuralSemantics`: order-independent structural equations.
- `StructuralDependency`: semantic dependency rules and the base at-most-one
  proposition, independent of schedule construction.
- `CertifiedComposition`: certified child collections, their derived composite
  structures, and the generic law for applying a child certificate to its part
  of a valid parent proposal.
- `CertifiedSchedule`: named certified-child rule schedules, schedule
  combination/coverage, finite-family scheduling both from an empty prefix and
  after existing availability, and generic parent at-most-one proof.
- `ModuleCycleContract`: behavioral rule declarations and coverage.
- `ModuleCycleEvaluation`: public contract evaluation relations/functions plus
  private typed assembly proofs.
- `ModuleCycleCertified`: the generic one-cycle implementation property and
  non-vacuous certified bundle.
- `Contracts/NoResetFifo*`: implementation-independent FIFO traces, finite
  temporal execution, and module-facing capacity/latency views.
- `Primitives/`: one file per concrete primitive, containing its structural
  definition and cycle contract; `PrimitivePorts` contains only shared
  single-bit port shapes.
- `Modules/`: one file per reusable module, containing its interface, hierarchy,
  wiring, structure, and cycle contract where present. Test-only module fixtures
  stay in `Examples/`. Temporal properties remain in separate `*Temporal`
  files rather than becoming part of structural module definitions.
- `FIRRTL/`: executable naming, generic hierarchy traversal, and direct text
  generation. Module-specific files assign names to existing structures; they
  do not define alternate circuits.

The former `StructuralRules` and `StructuralEvaluation` layers have been
removed. Their schedules mixed semantic dependency evidence with a program
that selected one structural solution. No current module or proof requires
that selected evaluator: structural existence is carried propositionally by
certificates, while certified schedules prove uniqueness without defining the
meaning of evaluation.

## Deliberate omissions and remaining pressure tests

There is currently no general automatic refinement composition, lowering,
backend correctness proof, reset model, or negative cycle checker. The trace
layer covers the no-reset one-entry FIFO and generic serial temporal
composition; a reusable serial `ModuleStructure` is not yet present in Silean 2.
Aggregate projection/assembly and `Fin`/tuple-position indexed instance
authoring are now validated by the recursively certified register and direct
FIRRTL generation.

The recursive register and leafwise Mask/BitwiseOr modules validate both
stateful and combinational aggregate decomposition. Generic Mux validates
contract-level composition of those recursive children, generic
EnabledRegister validates their stateful composition, and generic OneEntryFifo
validates a typed payload path with bit-valued handshake control. Direct FIRRTL
generation is now the major executable structural consumer.

## Direct FIRRTL generation

`ModuleNaming structure` is executable metadata indexed by the exact public
`ModuleStructure`. It supplies module, port, instance, adapter, primitive-state,
and recursive child names without copying wiring or behavior. Primitive
operation metadata is also indexed by the exact supported single-bit primitive.

`FIRRTL.renderCircuit` traverses that structure directly. It collects shared
module definitions, declares ports and child instances, renders splitters and
combiners as aggregate projection/assembly, and emits each typed structural
connection as a FIRRTL `connect`. No lowered circuit or generated wire table
intervenes. Runtime validation rejects illegal or duplicate local identifiers,
rendered module-name collisions, and reuse of one module key for two different
rendered definitions.

The backend adds `input clock : Clock` uniformly to every emitted module and
connects the parent clock to every child. This clock is infrastructure, not an
ordinary `ModulePorts` signal. The bit-register primitive emits a reset-free
FIRRTL register driven by that clock; recursive aggregate registers receive it
through their hierarchy.

Executable Lean checks cover BitMux, a vector Register, a tuple
EnabledRegister, and a vector-payload OneEntryFifo. The pinned external pipeline
also compiles emitted FIRRTL with CIRCT `firtool`, compiles the resulting
SystemVerilog with Verilator, and checks behavior with cocotb.

The checked-in Nix flake now supplies CIRCT `firtool`, Verilator, cocotb, Make,
Python, and Elan as one pinned development environment. Concrete designs are
selected by small typed Lean executables under `Silean2/Emitters/`; the shared
`FIRRTL.emitMain` handles only rendering errors, stdout, and `--output PATH`.
The Makefile keeps the external validation path file-oriented:
Lean produces `.fir`, `firtool` produces `.sv`, and cocotb runs that result in
Verilator. Generated artifacts stay below `build/` and are not semantic or
proof inputs.

Recursive tuple field labels are FIRRTL naming metadata rather than part of
`ModuleStructure`. The same naming description is propagated through generic
FIFO, mux, logic, register, splitter, and combiner renderings, so a payload
field such as `b.d[1].f` retains that hierarchy through FIRRTL and flattened
SystemVerilog. The structured FIFO cocotb test verifies all payload leaves
through capture, backpressure, simultaneous replacement, and dequeue.

## One-entry FIFO temporal contract

The no-reset FIFO layer is independent of module structure. A trace records
accepted transfers and logical contents at its boundaries; its contract states
exact conservation, a capacity bound, and a ready-propagation stall bound.
Generic finite execution lifts single-cycle conservation and stall inequalities
to arbitrary input sequences.

`OneEntryFifo.Temporal.step` invokes `ModuleCycleContract.evaluate` for the
existing generic FIFO cycle contract. It does not duplicate the FIFO transition
function and does not inspect child instances. Logical contents are empty when
`storedValid` is false and contain exactly `storedData` otherwise. The resulting
proofs establish single-cycle and whole-run conservation, capacity one, and
zero-cycle ready propagation for every `SignalType` payload.

`ModuleCycleCertified.solution_matches_evaluate` is the generic bridge back to
hardware structure: every structurally valid proposal has the contract
evaluator's outputs, and its next structural state corresponds to the
evaluator's next contract state. Thus temporal execution is deterministic at
the public contract boundary while certification proves the structure follows
that execution; no structural evaluator or proof schedule is exposed.

## Serial FIFO temporal composition

Serial composition is proved entirely over FIFO observations. `SerialCycle`
states the nine equalities connecting the external and internal valid/data/ready
signals; `SerialCycles` lifts those equalities pointwise over a finite trace.
The derived laws identify external transfers, cancel internal transfers, and
relate the three ready-stall counts.

`Contract.serial` uses only those laws and the two child contracts. Downstream
contents precede upstream contents in dequeue order, conservation cancels the
internal channel, capacities add, and ready-propagation latencies add. The
generic execution `Serial` lifts a one-step decomposition to every finite run;
the module-view `Constructor` then turns child satisfaction certificates into
parent satisfaction without referring to `ModuleStructure`.

A two-stage check pairs two `OneEntryFifo` contract states and wires two
`OneEntryFifo.Temporal.model` steps. Its view has capacity 2 and ready latency
0, and its satisfaction proof is obtained solely by the generic constructor
from the two capacity-1 child certificates. Each child contract execution is
connected to its certified structure by `solution_matches_evaluate`.

## Current review conclusion

The foundation now expresses the intended hierarchical argument cleanly:

1. readable structural equalities have an order-independent meaning;
2. named child-contract schedules prove rule-local availability and uniqueness
   without exposing child proof construction;
3. independent behavioral contracts are proved consistent with those
   equalities through preserved state correspondence; and
4. certified existence plus structural uniqueness gives exactly one result
   without making a public evaluator part of module composition.

The bidirectional two-child regression is now decisive: neither child can be
scheduled first if collapsed to a whole-child dependency, while the independent
forward and backward contract rules admit opposite valid orders. This adopts
generic certified-rule derivation as the normal hierarchical child interface.

No second lowered semantic representation is needed for this argument. Proof
verbosity that remains in concrete refinement checks comes mostly from exposing
the exact wiring equations of those examples; it has not justified adding
module-specific public helper APIs.

## Generic FIFO hierarchy

The FIFO now demonstrates the intended layering at arbitrary positive depth:

- `Fifo.Behavior` describes forward data/valid, backward ready, and next state.
  Serial behavior combines states with a labelled sum.
- `SerialFifo` is the two-instance structural composition. Its schedules call
  only public upstream and downstream contract rules, and its certification
  consumes only public child certificates.
- `Fifo.moduleStructure`, `Fifo.behavior`, and `Fifo.cycleContract` are
  independently computable. `Fifo.certification` is noncomputable evidence
  connecting those values.
- `Fifo.Temporal` executes the cycle contract and supplies the generic serial
  execution decomposition. Recursive views inherit the serial conservation
  theorem, yielding exact capacity `depth` and zero ready latency.
- `FifoNaming.depthNamingWith` is backend-only metadata with depth-sensitive
  module keys and recursively propagated payload labels.

This replaces the temporary two-stage example as the reusable architecture;
that example remains only a small regression check.
