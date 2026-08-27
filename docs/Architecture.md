# Silean 2 architecture

This is the authoritative description of the current design. `Roadmap.md`
records only the present direction and remaining work; `SourceMap.md` maps the
concepts here to files.

## Purpose

Silean 2 gives a readable, typed, HDL-like hierarchy
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

`StructuralExecution.lean` lifts this same meaning across clock cycles without
introducing a contract or chosen evaluator. `ModuleStructure.Transition` hides
one satisfying `ProposedValues` while exposing only its boundary outputs and
derived next structural state. `ModuleStructure.Executes` chains those
transitions over concrete input and output lists, carrying each intermediate
structural state through its inductive constructors. Nil, cons, singleton,
append, split, and length laws expose the ordinary finite-trace behavior.

Per-cycle `HasSolution` supplies non-vacuous totality, while the existing
`HasAtMostOneSolution` supplies determinism. Their conjunction,
`HasExactlyOneSolution`, lifts to existence and uniqueness of the complete
output list and final state for every finite input list. These are propositions,
not a noncomputable simulation function; a future executable simulator would
need a constructive algorithm proved to satisfy the same structural relation.

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

`Foundation/SignalExpectation.lean` supplies contract-independent partially
specified values for future behavioral contracts. A `BitExpectation` is
`zero`, `one`, or `dontCare`; `SignalType.Expectation` preserves vector and
tuple hierarchy by placing those choices only at bit leaves. Labelled
`SignalMap.Expectations` preserve the ordinary port labels. The generic
`Matches` relations are componentwise, exact expectations match exactly one
concrete value, and all-don't-care expectations match every value. This is
value vocabulary shared by contract forms.

`ModuleResetContract` is the second behavioral contract form. It owns an
arbitrary Lean state type, a distinguished bit reset input, a reset state, and
one natural step function producing ternary output expectations and next
state. Its finite-trace relation begins unsynchronized: ordinary cycles before
the first reset accept arbitrary outputs. A reset cycle also accepts arbitrary
outputs and synchronizes the specification state to `resetState`; every
following ordinary cycle must match the step function on that same cycle.
Repeated resets restart synchronization. The contract contains no structure,
cycle contract, structural-state mapping, evaluator, or certification proof.

`Foundation/Execution.Trace` supplies the generic relational finite-trace
mechanics used here and by structural execution, including nil, cons, append,
split, length, and decomposition laws. It does not prescribe deterministic
steps or hardware meaning.

## Structural-to-contract refinement

`ImplementsResetContract structure resetContract` is the direct multi-cycle
refinement used by reset-synchronized contracts. It says every relational
structural execution, from every possible initial structural state, has an
output trace accepted by the contract. This single statement is deliberately
stronger than mentioning only traces whose first cycle resets: pre-reset
outputs are unconstrained by `Accepts`, while any reset in the trace starts the
exact-cycle obligations and every later reset restarts them.

`ModuleResetCertified` packages the independently chosen structure and reset
contract with structural `HasSolution` and that refinement proof. Totality
prevents refinement from holding merely because the structure has no
executions; it also supplies an execution, and an accepted execution, for every
initial structural state and finite input trace. It does not require structural
uniqueness and stores no specification-to-structure state relation, schedule,
evaluator, or cycle contract. Its public laws expose acceptance of a whole
execution and matching of the suffix after either an initial reset or a reset
following an arbitrary prefix. Proofs may use private witnesses, but those
witnesses are not part of certification's meaning.

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
- generic Constant: the bit case wraps a Boolean constant primitive. Vector
  and tuple cases have no input splitters; they recursively instantiate the
  value selected for each immediate component and combine the outputs. Module
  keys include both signal shape and flattened value bits so distinct constant
  definitions cannot collide during FIRRTL collection.
- generic balanced Reduction: a reusable structural recursion accepts a
  certified same-typed binary child and certified identity source. Empty,
  singleton, and binary-node cases share generic existence, schedule-based
  uniqueness, and refinement proofs. The balanced constructor proves its leaf
  count and that every recursive split differs by at most one leaf.
- bit `All`: the structure instantiates Reduction with AND and constant true,
  but its public contract is phrased independently as the ordinary Lean
  `every` operation. Its public law says the result is true exactly when every
  indexed input is true. Tree shape and parenthesization remain details of the
  structural certification, not facts required of module users.
- generic recursive Equality: the public contract is the natural recursive
  `SignalType.equal` function, with a theorem relating a true result to Lean
  equality. A bit wraps the equality primitive. Each aggregate level splits
  its two inputs, recursively compares corresponding immediate components,
  and sends that indexed family of result bits to `All`. Empty aggregates are
  therefore equal by the identity behavior of `All`; no flattened bit order is
  part of either the contract or structure.
- generic VectorConcat: two vectors with a common element type are split into
  elements and recombined in left-then-right index order. Its contract is the
  natural `Fin.addCases` function, and public laws describe each half without
  exposing the splitter/combiner implementation.
- generic BinaryToOneHot: the public contract identifies the sole true output
  by the natural-number value of LSB-first input bits. The implementation
  recursively decodes the lower-index bits, masks two copies using the high bit
  and its inverse, and concatenates them. Thus the contract does not expose the
  recursive hierarchy or its scheduling proof.
- generic VectorSplit: one vector is partitioned into left and right subvectors
  using the existing element splitter and two combiners. It is reusable wiring
  structure, not a new primitive adapter case.
- generic CombMuxTree: the public contract directly indexes a value vector by
  the natural-number interpretation of an LSB-first selector. Each recursive
  level partitions the values, evaluates two smaller trees using the
  lower-index selector bits, and chooses with generic `Mux`; this hierarchy is absent from the
  consumer-facing contract.
- generic RegisterBank: the public state is a vector of entries, combinational
  reads observe the current vector, and the next-state rule functionally
  replaces only the decoded write entry. Its structure uses the certified
  decoder, a family of AND gates and enabled registers, a vector combiner, and
  CombMuxTree. State correspondence is pointwise over the register family;
  neither that hierarchy nor its schedules appear in the behavioral contract.
- HalfAdder: two bit inputs feed closed XOR and AND primitive children. Separate
  contract rules expose `sum` and `carry`, while the public numeric law states
  `sum + 2 * carry = left + right`; schedules and child identities are private.
- Increment: one LSB-first vector is incremented modulo its width. The public
  contract is natural vector arithmetic; a private carry-aware recursion fixes
  the initial carry to true, certifies the lower indices first, and feeds their
  carry into a HalfAdder for the current highest index.
- generic ResetRegister and EnabledResetRegister: synchronous reset is ordinary
  certified structure, not primitive behavior. ResetRegister selects between a
  configured Constant and its input before a generic Register.
  EnabledResetRegister uses ResetRegister as its storage child and adds
  enable/hold feedback through a generic Mux. Their natural contracts give
  reset priority over loading and retention; configured reset values are also
  included in their emitted module identities.
- generic EnabledResetCounter: a two-child stateful composition feeds the
  current output of EnabledResetRegister through Increment and returns the
  incremented vector to the register. Its independent contract states
  synchronous reset priority, modular enabled increment, and disabled
  retention directly. Increment stays in this state-owning layer rather than
  leaking into combinational pointer control. The construction and all
  certification machinery are private.
- FifoPointerControl: a certified combinational boundary interprets
  LSB-first read and write pointers whose final bit is a wrap bit. It exposes
  read/write addresses, non-fall-through valid/ready decisions, and separate
  read/write advance enables. Equal pointers mean empty; matching addresses
  with unequal wraps mean full. It has no reset input because it owns no state;
  Fifo supplies the current values of its two EnabledResetCounter
  pointer children here. Its structure splits the pointers directly
  into bits, recombines only address bits, compares addresses once and wrap
  bits once, and derives the remaining results with ordinary bit gates. The
  whole-pointer vector remains useful for Increment but is not redundantly
  compared here.
- generic Fifo: the scalable pointer-and-register-bank FIFO has exactly
  four children: read and write EnabledResetCounter instances,
  FifoPointerControl, and RegisterBank. Its independent contract state is the
  two logical pointers plus stored entries. Reset synchronously returns both
  pointers to zero without clearing storage, while valid/ready transfers drive
  independent pointer advances and accepted writes. Current-cycle handshakes
  and the ordinary bank write use pre-edge state even when reset is asserted;
  reset wins in the pointer next states. Child schedules,
  construction, structural-state correspondence, and refinement remain
  private. Independently, `Fifo.resetContract T addressWidth` describes the
  reset-synchronized behavior with the natural Lean state `List T`. Empty and
  nonempty queues determine ready/valid and head-data expectations directly;
  invalid output data is `dontCare`. Its total ordinary step removes an
  accepted output and appends an accepted input, with capacity derived solely
  from `2 ^ addressWidth`. This contract imports only the FIFO interface and
  is connected to the canonical structure by `Fifo.resetCertified`.
  Address width zero is the ordinary one-entry member of this family.

The FIFO reset certification is a direct concrete proof. It starts from the
existing cycle certificate's existential cycle state for an arbitrary
structural state. Before reset, it carries only that private correspondence and
places no requirements on outputs. A reset evaluation establishes zero
pointers, the invariant, and empty logical contents without assuming the
initial state was reachable. Ordinary cycles then use three public logical
observation equations and the four queue-update laws to match the reset
contract while preserving capacity. The local trace induction carries this
evidence through every later reset. None of the cycle state, structural-state
correspondence, invariant, or induction witness occurs in the resulting
`ModuleResetCertified` value. Structural totality is carried separately from
that private correspondence, using the FIFO's existing cycle certification.

This concrete proof suggests a possible future generic constructor would need
three proof ingredients: initial implementation-state coverage, reset
establishment of behavioral alignment, and ordinary-cycle output matching with
alignment preservation. Those ingredients would remain proof inputs rather
than fields of the resulting certificate. The pattern has not been extracted
yet; one example is not enough evidence that the abstraction would simplify
another certification.

This distinction is intentional: proof-facing helper contracts may expose the
precise behavior needed to compose a generic construction, while the reusable
module at the boundary owns the most natural Lean statement of its behavior.
Implementation choices such as balanced parenthesization must not leak into a
consumer-facing contract when a simpler mathematical description is
available.

`LeafwiseComposition` now centralizes the common split/component/combine
hierarchy, component-family scheduling, and structural-existence proof used by
Constant, Register, Mask, and BitwiseOr. Empty input families let Constant omit
splitters while retaining the same component and combiner machinery. State
correspondence and refinement remain module proofs because they express
constant generation, storage, masking, and disjunction semantics rather than
hierarchy mechanics.

The structural vocabulary also expresses a generic one-entry fall-through
FIFO. `OneEntryFifoControl` computes bit-valued upstream readiness and the shared
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

BitMux, OneEntryFifoControl, generic Register, Mask, BitwiseOr, Mux, EnabledRegister,
and OneEntryFifo all follow this boundary. Their public structures are
computable; their proof implementations are opaque.

## File responsibilities

- `Foundation/`: signal shapes, finite labels, fixed-width bit-vector
  arithmetic, typed signal maps and selections, connectivity-only module
  ports, and structural-state shapes.
- `Structure/`: named child interfaces, typed endpoints, total wiring, module
  bodies, and recursively owned module structures.
- `Primitive`, `PrimitivePorts`, and `Primitives/`: the open primitive record,
  shared bit-port shapes, and one file per supported single-bit primitive.
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
- `LeafwiseComposition`: generic recursive/fixed input classification,
  split/component/combine hierarchy and wiring, certified child occurrences,
  component-family scheduling, and composite structural-existence construction.
- `Modules/Reduction`: generic finite reduction shape, balanced-tree proof,
  hierarchy construction, schedules, and recursive certification.
- `Modules/All`: the AND/true instantiation, its natural all-inputs contract,
  public behavioral theorem, and module-owned naming.
- `Modules/Equality`: natural equality contract, recursive split/compare/All
  hierarchy, certification, public equality theorem, and module-owned naming.
- `Modules/VectorConcat`: natural vector concatenation contract,
  split/split/combine hierarchy, certification, public half-index laws, and
  module-owned naming.
- `Modules/BinaryToOneHot`: numeric one-hot contract, recursive
  split/decode/mask/concat hierarchy, certification, public selected-index
  law, and module-owned naming.
- `Modules/VectorSplit`: natural vector partition contract,
  split/combine/combine hierarchy, certification, public half laws, and
  module-owned naming.
- `Modules/CombMuxTree`: natural numeric-selection contract, recursive
  partition/two-subtree/mux hierarchy, certification, public selected-value
  theorem, and module-owned naming.
- `Modules/RegisterBank`: natural vector-state read/write contract,
  decoder/gate/enabled-register-family/combiner/mux structure, pointwise state
  correspondence, certification, public read/write/retention laws, and
  module-owned naming. Its private named child-instance type keeps proofs and
  naming independent of enumeration encoding; numeric selection is the shared
  `BitVector.toIndex` arithmetic utility also used by `CombMuxTree`.
- `Modules/HalfAdder`: natural Boolean and numeric two-bit addition contract,
  private XOR/AND composition and schedules, public result laws, and
  module-owned naming.
- `Modules/Increment`: natural modular-increment contract and public numeric
  law, backed by a private recursive ripple-carry hierarchy of HalfAdders and
  ordinary vector adapters.
- `ModuleCycleContract`: behavioral rule declarations and coverage.
- `ModuleCycleEvaluation`: public contract evaluation relations/functions plus
  private typed assembly proofs.
- `ModuleCycleCertified`: the generic one-cycle implementation property and
  non-vacuous certified bundle.
- `Contracts/NoResetFifo*`: implementation-independent FIFO traces, finite
  execution, and module-facing capacity/latency views.
- `Primitives/`: one file per concrete primitive, containing its structural
  definition and cycle contract; `PrimitivePorts` contains only shared
  single-bit port shapes.
- `Modules/`: one file per reusable module, containing its hierarchy, wiring,
  structure, and cycle contract where present. Test-only module fixtures stay
  in `Examples/`. Shared FIFO interface, cycle behavior, execution, and derived
  properties have separate files because they have different ownership.
- `Naming/`: generic typed naming metadata plus primitive and signal-adapter
  naming. Each reusable module owns its specific naming alongside its structure.
- `FIRRTL/`: generic hierarchy traversal, validation/rendering, and emission.
  It consumes naming metadata and does not define alternate circuits.
- `Examples/Fixtures/`: small test-only module structures shared by checks.
- `Examples/Checks/`: compile-time and executable regressions.

The former `StructuralRules` and `StructuralEvaluation` layers have been
removed. Their schedules mixed semantic dependency evidence with a program
that selected one structural solution. No current module or proof requires
that selected evaluator: structural existence is carried propositionally by
certificates, while certified schedules prove uniqueness without defining the
meaning of evaluation.

## Deliberate omissions and remaining pressure tests

There is currently no general automatic refinement composition, lowering,
backend correctness proof, reset model, or negative cycle checker. The trace
layer covers the no-reset one-entry FIFO and generic serial execution
composition, while `SerialFifo` and `Fifo` provide reusable structural
composition at arbitrary positive depth. Aggregate projection/assembly and
`Fin`/tuple-position indexed instance
authoring are now validated by the recursively certified register and direct
FIRRTL generation.

The recursive register and leafwise Mask/BitwiseOr modules validate both
stateful and combinational aggregate decomposition. Generic Mux validates
contract-level composition of those recursive children, generic
EnabledRegister validates their stateful composition, and generic OneEntryFifo
validates a typed payload path with bit-valued handshake control. Direct FIRRTL
generation is now the major executable structural consumer.

## Direct FIRRTL generation

`Naming.ModuleNaming structure` is executable metadata indexed by the exact public
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

## One-entry FIFO properties

The no-reset FIFO layer is independent of module structure. A trace records
accepted transfers and logical contents at its boundaries; its contract states
exact conservation, a capacity bound, and a ready-propagation stall bound.
Generic finite execution lifts single-cycle conservation and stall inequalities
to arbitrary input sequences.

`NoResetFifo.Execution.step` invokes `ModuleCycleContract.evaluate` for any
`NoResetFifo.CycleBehavior`. `OneEntryFifo.Properties` specializes that one generic
interpreter; it does not duplicate an evaluator or inspect child instances.
Logical contents are empty when `storedValid` is false and contain exactly
`storedData` otherwise. The resulting proofs establish single-cycle and
whole-run conservation, capacity one, and zero-cycle ready propagation for
every `SignalType` payload.

`ModuleCycleCertified.solution_matches_evaluate` is the generic bridge back to
hardware structure: every structurally valid proposal has the contract
evaluator's outputs, and its next structural state corresponds to the
evaluator's next contract state. Thus contract execution is deterministic at
the public contract boundary while certification proves the structure follows
that execution; no structural evaluator or proof schedule is exposed.

## Serial FIFO execution and property composition

Serial composition is proved entirely over FIFO observations. `SerialCycle`
states the nine equalities connecting the external and internal valid/data/ready
signals; `SerialCycles` lifts those equalities pointwise over a finite trace.
The derived laws identify external transfers, cancel internal transfers, and
relate the three ready-stall counts.

`Contract.serial` uses only those laws and the two child contracts. Downstream
contents precede upstream contents in dequeue order, conservation cancels the
internal channel, capacities add, and ready-propagation latencies add. The
generic execution `Serial` lifts a one-step decomposition to every finite run;
`View.Execution.Constructor` then turns child satisfaction certificates into
parent satisfaction without referring to `ModuleStructure`.

`NoResetFifo.Execution.serial` proves that execution of a serially composed cycle
behavior decomposes into execution of its children. `SerialDepthFifo.Properties` combines
the child views using the generic no-reset FIFO constructor. Positive-depth
FIFO checks exercise this composition at depths one, two, and three; no second
hand-written two-stage evaluator is retained.

## Resettable FIFO behavioral correctness

The canonical pointer-and-register-bank `Fifo` is interpreted at its public
cycle-contract boundary. `Fifo.Properties` defines logical occupancy as the
circular distance between its extended read and write pointers and defines
logical contents by reading that many register-bank entries from the read
address. The reachable-state predicate is precisely the capacity bound on that
distance; it rules out the unused half of the extended-pointer state space.

Reusable arithmetic about circular distance, index advancement, logical reads,
and functional writes lives in `Foundation/CircularBuffer.lean`.
`Foundation/Execution.lean` contains contract-independent deterministic-run
and relational-trace mechanics over finite input lists. Reset-aware
accepted-transfer and finite-transition
semantics lives in `Contracts/ResetFifo.lean`. The module property layer proves from
`ModuleCycleContract.evaluate` that every valid cycle preserves the invariant
and obeys the logical queue equation. Reset cycles accept no logical transfer
and clear the next logical contents; ordinary cycles append accepted input and
remove exactly the oldest accepted output. This covers stalls, simultaneous
transfers, pointer wraparound, and capacity one uniformly.

The generic finite-run induction then proves the transition relation for every
input sequence. Reset-free segments have exact conservation; from empty, their
accepted outputs are a prefix of accepted inputs. This is the ordering and
no-loss/no-duplication theorem. Structural certification remains a separate
fact: none of these behavioral proofs sees child instances, wiring, or private
schedules.

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

## No-reset serial-depth FIFO hierarchy

The FIFO now demonstrates the intended layering at arbitrary positive depth:

- `NoResetFifo.CycleBehavior` describes forward data/valid, backward ready, and next state.
  Serial behavior combines states with a labelled sum.
- `SerialFifo` is the two-instance structural composition. Its schedules call
  only public upstream and downstream contract rules, and its certification
  consumes only public child certificates.
- `SerialDepthFifo.moduleStructure`, `SerialDepthFifo.cycleBehavior`, and
  `SerialDepthFifo.cycleContract` are independently computable.
  `SerialDepthFifo.certification` is noncomputable evidence
  connecting those values.
- `NoResetFifo.Execution` executes cycle contracts and supplies the generic serial
  execution decomposition. `SerialDepthFifo.Properties` recursively combines certified
  views, yielding exact capacity `depth` and zero ready latency.
- `SerialDepthFifo.Naming.depthNamingWith` is module-owned metadata with depth-sensitive
  module keys and recursively propagated payload labels.

This replaces the former hand-written two-stage evaluator with one reusable
architecture and checks the same behavior through positive-depth FIFO tests.
