# Silean 2 foundational design

## What exists

The current foundation contains thirty-one ideas:

1. `SignalType` describes bits, fixed-length vectors, and anonymous ordered
   tuples, including arbitrary nesting.
2. `SignalType.Denote` gives each structural type its Lean value type.
3. An `Enumeration` gives every member of a finite identity type one stable,
   executable position.
4. An `EnumeratedMap` adds a total value function to such an identity type and
   shares its ordered traversal and lookup laws across uses.
5. A `SignalMap` is an `EnumeratedMap SignalType`; it gives ordinary symbolic
   labels types and derives an anonymous structural shape.
6. A `SignalMap.Values` assigns every label a value of its computed signal
   type.
7. `ModulePorts` contains only readable input and output maps used for
   connectivity; `ModuleSignature` contains their anonymous shapes.
8. `StructuralState` is either primitive-local signals or a recursively
   labelled collection of child-instance states.
9. `Primitive` is a closed, finitely enumerated set of single-bit leaf
   identities and determines its readable ports.
10. `Primitive.localState` explicitly declares a leaf's structural state.
11. `Instances` gives symbolic instance names canonical order and maps each name
   directly to the exact `ModulePorts` required from its child definition.
12. `SignalSource` and `SignalSink` give module-boundary and instance ports one
    generic endpoint representation indexed by structural signal type.
13. `Wiring` totally assigns a same-typed source to every sink.
14. `EndpointContext` binds the module ports and instances once for authoring.
15. `ModuleBody` owns an endpoint context and its complete wiring without
    owning semantics or an evaluation order.
16. `emptySignalMap` is the one state map for modules with no storage; it does
    not introduce a separate combinational module kind.
17. `SignalSelection` records an ordered selection of readable signal labels
    and the heterogeneous structural type of their values.
18. `CycleOutputRule` states exact input reads, output writes, and the required
    output function from selected inputs and complete current state.
19. `CycleStateRule` gives every contract one total transition from all inputs and
    current state to next state.
20. `ModuleCycleContract` owns an independent contract-state map, finite output-rule
    identities, and proof that their writes cover every output exactly once.
21. Each independent primitive value lives in its own `Primitives/` file with
    its rule-based contract over the same ports and local state.
22. `ModuleStructure` is either a primitive leaf or a composite owning only its body and
    one correctly typed child `ModuleStructure` for every instance.
23. `ModulePath` and `PrimitiveOutputOccurrence` distinguish recursively
    instantiated hardware occurrences from reusable child definitions.
24. `StructuralState.Values` and `ModuleStructure.State` give recursively labelled
    structural state its Lean value type.
25. `ProposedValues` stores outputs at every module occurrence, primitive next
    state at leaves, and recursively proposed child values at composites.
26. `Primitive.OutputsSatisfy`, `Primitive.NextStateSatisfy`, and
    `Primitive.IsSolution` give each primitive structural equations
    independently of contracts.
27. `SignalSource.value` and `ProposedValues.childInputs` derive wire and child
    input values without storing them in a proposal.
28. `ModuleStructure.IsSolution` recursively checks primitive equations, child
    solutions, and boundary wiring without specifying an evaluation order.
29. `ModuleCycleContract.EvaluatesTo` gives contracts an independent, order-free
    one-cycle meaning; exact rule coverage generically yields a unique result
    and the deterministic `ModuleCycleContract.evaluate` function.
30. `Implements` proves that every structural solution agrees with a
    contract evaluation and preserves an explicit state correspondence.
31. `ModuleCycleCertified` packages structure, cycle contract, a non-vacuous
    state correspondence, and their implementation proof.

There are independent order-independent structural and contract relations,
each with generic existence and uniqueness results, connected by one-cycle
contract refinement for Mux, DualNot, and EnabledRegister.

## Compositional uniqueness proof

At-most-one compares two `ProposedValues` that both satisfy `ModuleStructure.IsSolution`
for the same external inputs and current structural state. It does not redefine
circuit meaning and should not require a separate public `Acyclic` predicate.

The positive evidence is a complete availability-ordered application
of **structural rules**. These are distinct from behavioral `ModuleCycleContract`
output rules. A structural rule records the precise input values required to
determine particular outputs. Hierarchical composition translates child-rule
reads through parent wiring, preserving per-output dependencies rather than
treating every child output as depending on every child input.

`StructuralSchedule.finishAgreement` inductively maintains the child-output
occurrences already proved
equal in the two proposals. Root inputs and current state are equal initially.
At each rule application, every read is either initial or already proved equal;
the primitive equation or child rule therefore forces the written outputs to
be equal. Complete rule coverage establishes equality of every stored output.
Once every child output agrees, identical derived child inputs let the generic
parent theorem invoke each child's uniqueness theorem. Boundary wiring then
forces equal parent outputs, giving equality of the complete proposals.

Primitive rules and primitive uniqueness are proved once. Generic composition
produces reusable parent structural rules as well as parent uniqueness.
NOT, Mux, HierarchicalDualNot, RepeatedDualNot, and EnabledRegister exercise
the construction. EnabledRegister schedules the register output before the mux:
the apparent feedback is broken by current state, without a cycle predicate.

A complete rule-availability derivation is constructive evidence that no
unresolved same-cycle cycle was introduced. A separate negative cycle concept
will be added only if later machinery needs one. `ExecutableStructuralRule`
adds a program to a semantic structural rule and proves that the program
depends only on declared reads and agrees with every satisfying proposal on
declared writes. It does not replace the rule or `ModuleStructure.IsSolution`.

`StructuralSchedule.execute` starts from canonical placeholder values and computes
child outputs in availability order. Placeholders are never semantically read:
each call proves its reads available, and each write is fresh. At completion,
the generic replay proof shows that the computed output store agrees with the
proposals constructed by the child evaluators. This establishes the real child
input equations and boundary aliases, yielding `StructuralEvaluator.composite` and a
proof that its result satisfies `ModuleStructure.IsSolution`. Combining this evaluator
with compositional uniqueness yields exactly one solution.

Structural state and contract state are distinct. `ModuleStructure.structuralState`
recursively derives state from the actual child modules; `ModuleCycleContract.state`
independently owns the abstract state used to specify behavior. Neither is
stored in `ModulePorts`.

## Why the types are dependent

A symbolic label is an ordinary inductive value such as `.valid` or `.payload`.
Its `SignalMap.signalType` computes its structural type. Consequently `Values`
still cannot return the wrong value type, and a later connection can
require its source and sink to have exactly the same structural type without a
runtime check. This applies uniformly to scalar ports, vectors, and tuple
fields without requiring a `Sigma` enumeration of type-indexed labels.

Vectors denote functions from `Fin length` to element values. Tuples denote
heterogeneous ordered products. Their symbolic field names are intentionally
absent from `SignalType`, so two differently labelled views of the same ordered
field types have equal structural shape.

## Why enumeration stores proofs

`Enumeration` has three fields:

- `values` is the finite ordered data used by execution and later emission.
- `locate` constructively returns the position of every value. It provides
  completeness without search, decidable equality, or choice.
- `nodup` proves that a value does not occupy two positions. Later positional
  identity and deterministic emission need this uniqueness.

Both proof fields enforce a real invariant. Neither describes circuit behavior.
They disappear during execution and do not burden users of `ordinal`.

These capabilities are deliberately foundational because later machinery is
already known to need them:

- wiring and hierarchy need stable typed identities;
- exhaustive equation generation and evaluation need finite traversal;
- definition collection and Verilog emission need deterministic order; and
- correspondence proofs need a constructive identity-to-position map that does
  not reconstruct typed ports from raw numbers.

Silean 2 is not postponing these requirements. It retains their certified form
in `SignalMap` so every readable view and later consumer shares one source of
truth.

The record fields are the internal representation, not the authoring surface.
Ordinary finite identity types use `deriving Enumeration`. The deriving handler
accepts nonempty inductive types with any number of nullary constructors. It
uses declaration order for `values` and generates the matching `ListIndex` for
each constructor; Lean then elaborates and the kernel checks the generated
`nodup` proof and total lookup function. It does not require `DecidableEq`.

A working list-based prototype accepted a list, a `Nodup` proof, and a coverage
proof, then used decidable equality to compute `ListIndex`. It was rejected as
the authoring API because every declaration repeated its constructors in the
list and again in an exhaustive coverage proof. It was arity-independent but
did not remove the transcript. The deriving approach names each constructor
only in the inductive declaration and preserves that explicit order.

An alternative using `Fintype` was not adopted because it would still leave the
chosen stable order and constructive lookup to additional machinery.

## Structural and contract state

There are two state representations with different purposes:

```text
primitive structural state = explicitly declared local stored state
composite structural state = tuple(child instance name -> child structural state)
contract state             = abstract behavioral state chosen by the contract
```

The composite structural state is computed from hierarchy rather than joined
to children by a separately authored `StateConnections` map. Current state is
projected to each child by its instance label, and next structural state is
assembled from the children's next states using the same shape. This makes
state ownership total, unique, and type-correct by construction. Stateless
children may contribute zero-bit fields; a backend may erase those fields.

`ModulePorts` and `ModuleSignature` contain connectivity only. A complete
module is required before structural state can be requested, preventing a
separately declared state interface from disagreeing with the actual child
modules. `ModuleSignature` deliberately contains no:

- symbolic port identities;
- behavioral function or contract;
- names or strings;
- wiring or children;
- schedules or evaluation order; or
- validity wrapper duplicating the enumeration invariants.

There is still one module and contract model, not combinational and sequential
variants. Zero-bit structural and contract states handle combinational cases.
The two states need not have equal shapes.

## Rule-based contracts

`SignalSelection signals types` is a typed ordered selection from a
`SignalMap`. `selection.project values` returns exactly the heterogeneous value
shape recorded by `types`. The generic `signals.select label` and
`selection.prepend label` operations keep rule declarations symbolic; they do
not use positional port references.

An output rule is indexed by a contract and contains:

- the precise module inputs it reads;
- the module outputs it writes; and
- a target from those selected input values and the complete current-state
  values to the selected output values.

`ModuleCycleContract.OutputRulesHold` means every rule's typed assignment agrees
with one complete set of output values. `ModuleCycleContract.EvaluatesTo` adds
equality with the total state-rule result. Neither definition refers to rule enumeration
order. Exact, nonoverlapping coverage makes satisfying outputs unique.

`applyOutputRules` folds rule assignments into default values. The
defaults are unobservable because coverage proves every output is written, and
disjoint writes make construction order semantically irrelevant. Mux,
independent DualNot outputs, and stateful EnabledRegister exercise the same
generic machinery.

This retains the useful Silean rule model. The Mux contract has one rule that
reads select/false/true and writes result. The DualNot-shaped contract has two
rules: each reads one input and writes the corresponding output. Thus the
contract records independent observable cones without pretending to be the
structural meaning of the hierarchical implementation.

Every `ModuleCycleContract` owns its state map and one total `CycleStateRule`. Its target sees all
inputs and current state and returns the complete next state. For empty state,
the result is `SignalMap.emptyValues`; no combinational-specific rule or
contract is needed.

The flattened output write selections must be a permutation of the canonical
output labels. Since output labels are duplicate-free, generic theorems derive
both total coverage and non-overlap. A module author supplies one coverage
proof, not separate per-output uniqueness proofs.

The same representation fits an enabled register without modification: its
output rule can read no inputs and return current state, while its total state
rule selects between the input value and current state using enable. It also
fits FIFO contracts: forward and ready remain separate output rules with
different input selections, and the total state rule sees all handshake inputs.
Structural storage ownership and one-cycle meaning are tested separately by
EnabledRegister, and one-cycle refinement now connects them.

## One-cycle refinement

`Implements module contract StateCorresponds` quantifies over every
satisfying structural proposal at corresponding current states. It requires a
contract evaluation whose outputs are the proposal's boundary outputs and
whose next contract state corresponds to the proposal's derived next
structural state. This is independent of any chosen structural schedule or
evaluator.

Mux and hierarchical DualNot use the trivial correspondence between their
zero-bit contract state and zero-bit structural leaves. EnabledRegister relates
its one abstract stored bit to the `.storage` child's register bit. Its
preservation proof reuses the Mux refinement for the `.selection` child, then
uses the register equation to establish hold and update behavior.

This exercise showed that the relational contract form is useful: refinement
can directly require that all rules and the transition agree with a structural
solution. The contract assembly operation is ordinary deterministic evaluation,
however, so it is named `applyOutputRules`, with the combined public operation
named `evaluate`; no contract solving layer exists. Structural evaluators and
uniqueness were not needed by refinement because `Implements` deliberately
quantifies over every satisfying proposal.

## Certified cycle modules

`ModuleCycleCertified` is the public verified unit. It contains independent
`moduleStructure` and `cycleContract` fields, the state correspondence, the
`Implements` proof, and `hasCorrespondingState`. The last field requires every
structural state to have a contract interpretation, preventing certification
with an always-false relation.

No trace API is required for the current argument. `Implements` already proves
that correspondence is preserved from current to next state, so the same fact
can be iterated later if a consumer actually needs sequence packaging.

## Why tuple fields and ports share `SignalMap`

Both are readable labels for positions in an ordered structural shape. A
`SignalMap` owns one ordinary `Label` type, its finite enumeration, and a
`signalType : Label → SignalType` function. Mapping `signalType` over the
enumeration produces the anonymous shape.

For tuples, `signalMap.tupleType` produces the structural tuple. For modules,
`ModulePorts.signature` produces the structural signature. The foundation
example defines both `PacketField.valid/payload` and
`RenamedPacketField.enabled/data`; their `tupleType`s are definitionally equal.

These symbolic constructors are source-level identities, not output strings.
Final Verilog spelling and legalization remain a later naming layer.

## Why primitives are closed and single-bit

`Primitive` is an inductive identity with `not`, `and`, `or`, `eq`, and
`register`. Every primitive operates on bits. Vectors and aggregates will be
built compositionally rather than by parameterizing primitive identities. Its
port and local-state functions fix each leaf's interface. An arbitrary Lean
function cannot become a primitive by constructing a record.

Primitive meaning is defined separately in `StructuralSemantics.lean`. Combinational
outputs depend on inputs and preserve empty local state. The register output is
its current `.stored` bit and its next state is its `.input` bit. Keeping these
equations separate avoids mixing structural identity, semantics, and contracts.

## Why finite symbolic maps share one abstraction

`EnumeratedMap Value` packages a symbolic `Key` type, its canonical
`Enumeration`, and a total `value : Key → Value` function. Both `SignalMap` and
`Instances` are readable aliases of this same representation.
User-defined constructors such as `.payload` and `.inverter` remain the keys;
only generic storage and traversal operations are shared.

The generic layer proves that its ordered values have the same length as its
keys and that looking up the ordinal of a key returns that key's mapped value.
Later positional equation generation and emission can reuse those facts instead
of proving signal-specific and instance-specific versions.

## The instance layer

`Instances` is an `EnumeratedMap ModulePorts`: its keys are readable instance
names and its values are the exact interfaces those instances require. The NOT
body maps `.inverter` to `Primitives.not.ports`; a hierarchical body can map a
name to `DualNot.ports` in exactly the same representation.

The instance map deliberately stores neither a primitive/module tag nor an
external module identifier. Wiring needs only interfaces. The complete
`ModuleStructure.composite` constructor separately requires
`childStructure name : ModuleStructure (instances.ports name)`, so a missing or
port-incompatible implementation cannot be constructed.

## Generic typed endpoints

`SignalSource ports instances signalType` identifies something that
produces a signal: either a labelled module input or a labelled output of a
named instance. `SignalSink` identifies the two consumers: module outputs and
instance inputs. The final `signalType` index is computed from the selected
port, so differently shaped endpoints do not have the same Lean type.

Neither endpoint definition mentions `Primitive` or `ModuleStructure`. It reads the
interface stored at the instance name, so primitive and composite children use
the same endpoint constructors.

Direct dependent constructors do not give Lean enough context to elaborate
short labels such as `.inverter` and `.output` reliably. `EndpointContext`
packages the module boundary and instances once, then
provides `moduleInput`, `moduleOutput`, `instanceInput`, and `instanceOutput`.
Expressions such as `context.moduleInput .select` and
`context.instanceOutput .combine .output` retain symbolic labels without
repeating structural arguments. There are no casts, proof arguments, tactics,
or explicit `SignalType` annotations inside endpoint expressions.

A checked-in rejected-expression test was not added because Lean's negative
test mechanism would preserve compiler diagnostic text. The intrinsic result
index is the relevant guarantee: selecting a bit port constructs an endpoint
indexed by `.bit`, not one indexed by a vector or tuple shape.

## Total wiring and structural module bodies

`Wiring ports instances` contains one driver function for each
kind of sink:

- `moduleOutput` chooses a same-typed source for every boundary output;
- `instanceInput` chooses a same-typed source for every input of every named
  instance.

These functions are total, so an undriven sink cannot be constructed. Each
function returns exactly one source, while returning one source from several
calls represents fan-out. `Wiring.drive` presents both fields as one generic
function over `SignalSink`. Wiring contains no order, evaluation, acyclicity
certificate, or behavioral statement.

`EndpointContext` owns its labelled module boundary and ordered named instance
interfaces.

`ModuleBody` then owns that context and the complete type-correct wiring for it.

The NOT body maps `.inverter` to `Primitives.not.ports`. Its two clauses read as
direct connectivity:
the inverter input selects the module input `.value`, and module output
`.inverted` selects the inverter's `.output`.

Authoring binds `ports` and `instances` once in the context.
Endpoint expressions require only meaningful module or instance port labels.
Wiring is split into its two sink forms because that gives Lean enough dependent
context for ordinary exhaustive patterns; the derived `drive` function retains
the unified generic view.

The representation corresponds closely to the structural part of Verilog: a
module boundary, named instances of referenced definitions, and nets expressed
as drivers of every consumer. Names for eventual emission and module-definition
ownership are deliberately separate.

## Recursively owned modules and occurrences

`ModuleStructure ports` has two constructors. `.primitive gate` is the closed leaf at
`gate.ports`. `.composite body childStructure` owns a local body and requires a
child module at the exact interface recorded for every instance. It contains
no contract. `ModuleStructure.structuralState` returns `.local gate.localState` for a
leaf and an instance-labelled `.children` branch recursively computed from the
actual `childStructure` values for a composite.

The hierarchical DualNot owns two NOT leaves. RepeatedDualNot owns two child
instances and returns the same `HierarchicalDualNot.moduleStructure` value for both.
This is definition reuse. Traversal through `.first` and `.second` creates
different `ModulePath`s, so their nested NOT outputs are distinct hardware
occurrences even though both paths reach the same reusable definition.

`ModulePath` is the only hierarchy vocabulary added. A
`PrimitiveOutputOccurrence` pairs such a path with a primitive output label.
It retains typed occurrence identity for later equations without introducing
equations, evaluation, definition keys, or emitted names.

## Authoring cleanup and two-instance evidence

`EnumeratedMap.of Key value` is the only authoring constructor added after the
NOT review. It is generic over both key and value types and uses a derived
`Enumeration Key`; signal maps, tuple field maps, and instance maps all have
the same shape. It removes repeated record fields
without hiding identity order or the total value function.

Reusable designs are separated from test fixtures. Each file under `Modules/`
owns one useful module's interface, body, recursive children, and cycle contract
where one is defined. Each file under `Primitives/` similarly owns one
independent primitive value and its contract. Test-only modules, checks, and
cross-module certification proofs stay in `Examples/`.

The second inverter adds one constructor to the instance identity and one driver clause from the first
output to the second input. Both modules still explicitly declare their port
labels, signal types, ordered instances, wiring, and `ModuleBody` assembly.
Neither uses casts, proof arguments, tactics, or manual `SignalType` indices.
The only dependent matches are the exhaustive `Wiring` fields, where Lean uses
the selected instance and port to determine the required source type.

No macro was adopted. The two examples provide strong evidence for common
syntax, but weak evidence for its full shape because both have one-bit unary
boundaries and only NOT primitives. A general wiring macro must handle
heterogeneous port shapes, vectors and tuples, mixed component references,
canonical declaration order, and clear missing/duplicate/type mismatch errors.
A unary-interface helper, primitive-only body builder, or NOT-specific syntax
would be shorter but would encode the examples rather than the architecture.
The next heterogeneous module should supply the missing evidence before a DSL
is fixed.

## Branched mixed-interface evidence

The structural mux combines one unary NOT, two binary ANDs, and one binary OR.
Its eight sink clauses cover one module output and all seven primitive inputs.
The `.select` module input is selected as the source of both the inverter input
and the true-path selector input, demonstrating fan-out without another data
structure or proof.

The actual module files now measure 47 lines for NOT, 49 for DoubleNot, and 68
for Mux. Mux growth corresponds to two additional module inputs, three
additional instance names, heterogeneous component assignments, and six more
sink clauses. It adds no casts, proof arguments, tactics, explicit signal-type
indices, or framework types. Dependent matching remains confined to exhaustive
instance-input clauses and rejects the wrong port vocabulary or signal shape.

The mapping to a Verilog-like description is direct:

- `ModulePorts` declares the external interface;
- the ordered instance map declares named primitive/module uses;
- `Wiring.moduleOutput` supplies each output driver; and
- `Wiring.instanceInput` supplies every instance-input connection.

No intermediate net names are structural identities; later emission can assign
names to instance outputs when required.

The mux makes a future declarative syntax plausible, particularly a syntax that
lists labelled sinks and sources and expands into the existing total functions.
It still does not determine how that syntax should express aggregate ports or
module-definition references, nor how it should report duplicate and missing
sinks before elaboration. The recommendation is therefore to keep the current
representation as the stable macro expansion target but defer macro adoption
until one aggregate or hierarchical example has tested those cases. Semantic
work does not need to wait for that authoring layer.

## Readability review

The public paths through the foundation are still short:

```text
Enumeration -> EnumeratedMap -> SignalMap -> valuation / tuple type
                           |-> Instances -> component ports
                                         `-> SignalSource / SignalSink
                                                     `-> Wiring -> ModuleBody

SignalType -> ModulePorts -> ModuleSignature
                    |-> Primitive.ports
                    `-> SignalSelection -> CycleOutputRule --+
                         CycleStateRule -----------------------+-> ModuleCycleContract
```

A reader can understand a primitive signature from its port constructors and
`deriving Enumeration`. Constructor order establishes canonical order, while
generated declarations hide `nodup` and `ListIndex` plumbing.
There are no positional reference transcripts, casts, schedules, semantic
proofs, or module-specific tactics.

The certified enumeration remains inspectable because later generic proofs
use its fields directly. The deriving mechanism changes only how those fields
are constructed, not their kernel-checked representation.

## How this foundation uses lessons from Silean

The first project established several requirements that are adopted now rather
than rediscovered later:

- ports and child identities must be finite and canonically ordered;
- lookup evidence must be computational, not proposition-only;
- typed identities must survive until deliberate erasure;
- structure, contracts, evaluator orders, and emission metadata need distinct
  owners; and
- numeric port reconstruction and handwritten positional transcripts are not
  an acceptable generated proof path.

What is deferred is only material belonging to later layers, not requirements
whose eventual need is already clear.

## Questions deliberately left open

- Whether later module identity is indexed only by signature or carries some
  additional structural key.
- Whether aggregate or hierarchical authoring evidence justifies a declarative
  module/wiring macro.

State ownership is settled: each contract owns its abstract behavioral state,
primitive leaves own local structural state, and a composite's structural
state is derived from its actual child modules. State does not appear in the
connectivity-only module ports.

The order-independent structural equations are now fixed provisionally and
have been exercised through two hierarchy levels.

## Architecture checkpoint

The subsequent Silean-informed review found that the last sentence above was
too strong: module-definition ownership determines the recursive node and
equation domain, so it should be tested before those equations are fixed. See
`ArchitectureCheckpoint.md` for the classification of the current structures,
the representative Silean comparison, and the revised risk-ordered roadmap.

That checkpoint also retains Silean's useful rule and schedule concepts in
sharper roles. Output rules with exact read/write selections and one total
state rule form the uniform contract language. Schedules are optional derived
or supplied constructive evaluator certificates. Structural solutions remain the
independent meaning to which both schedule evaluation and contract refinement
are related.
