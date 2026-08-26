# Silean 2 roadmap

This is the chronological development record. Earlier goal outcomes sometimes
describe structures that later goals replaced; they are retained as history,
not as the current API. `ArchitectureCheckpoint.md` is the authoritative
current overview.

## Purpose

Silean 2 is a parallel design experiment. It starts from a small foundation
rather than preserving compatibility with the existing Silean representation.
The experiment will determine whether a clearer separation between circuit
structure, circuit meaning, behavioral contracts, proof certificates, and
Verilog emission produces a substantially simpler system.

The existing `silean` project remains intact and is the source of lessons and
reusable generic proofs. Silean 2 should copy an abstraction only after its role
in the new design is understood.

## Working principles

- Circuit structure is defined by typed ports, primitive instances, child
  instances, wiring, and storage.
- Behavioral contracts state desired behavior but do not define circuit
  equations.
- Every module has input and output maps plus structural state. Primitive state
  is explicit and composite state is derived from the child-instance hierarchy.
  Stateless modules use zero-bit state; there are not separate combinational
  and sequential module foundations.
- Contracts own a separate abstract state chosen for behavioral clarity. A
  refinement proof relates it to structural state, often by decomposing parent
  contract state and reusing child correspondences.
- Contracts use output rules with precise read/write selections plus one total
  next-state rule. Rules describe required observable behavior, not composite
  structure.
- An order-independent solution relation gives the circuit its meaning.
- Schedules are constructive evaluators and proof certificates, not semantic
  authority. Derive them where practical, allow supplied certificates where
  useful, and avoid duplicated positional transcripts.
- Naming and emission metadata do not participate in behavioral equality.
- Verilog generation should be a shallow, inspectable translation from the
  structural representation or a small emission plan.
- Proofs should be generic. ModuleStructure-specific work should primarily establish
  that a particular structure implements its contract.
- Do not introduce raw numeric IR as a prerequisite for semantic correctness.
- Do not add handwritten instance paths or positional port transcripts.
- Anticipate downstream machinery whose requirements are already known. In
  particular, retain canonical finite identity and constructive lookup in the
  foundation for wiring, solving, hierarchy traversal, and emission. Keep
  layers separate; do not postpone known invariants merely to make an early
  prototype smaller.
- Keep every focused Lean build below five seconds. If a focused proof reaches
  that limit, restructure it before proceeding.
- Do not use `sorry`, new axioms, `Classical.choice`, or `native_decide` to
  discharge new proof obligations.

Each goal ends with a review before the next goal begins. The review should
explain the non-proof structures in plain language, identify unresolved design
choices, and record focused build times. Later goals may be revised based on
that review.

## Goal 1: foundational vocabulary

Create the independent Lake package with only:

- recursive `SignalType` shapes for bits, vectors, and tuples;
- typed port families and valuations;
- finite, executable port enumerations;
- `ModuleSignature`; and
- a closed single-bit primitive vocabulary.

Add a few small typechecking or executable examples and concise design notes.
Do not add composite modules, behavioral contracts, circuit semantics,
schedules, state, aggregates, lowering, or rendering.

Review question: **Are the basic types for signals, ports, signatures, and
primitive identities understandable without knowing the proof machinery?**

### Goal 1 outcome

Completed with three small source layers:

- `Silean2/Types.lean` defines bit, vector, and anonymous tuple signal types;
  typed symbolic families and valuations; constructive list positions; finite
  enumerations; the shared `SignalMap` view; and structural module signatures.
- `Silean2/Primitive.lean` defines unary/binary Boolean port families and the
  closed `not`/`and`/`or`/`eq` primitive identities with their signatures.
  The later `register` addition remains single-bit and finitely enumerated.
- `Silean2/Examples/Foundation.lean` demonstrates valuations, canonical port
  order, executable ordinals, primitive arities, aggregate values, and two
  differently labelled field maps producing the same tuple type.

The only proof fields retained are `Enumeration.locate`, which makes lookup
total and executable, and `Enumeration.nodup`, which makes each ordinal unique.
There is no separate signature-validity wrapper. Primitive identities contain
no Lean behavior.

On the initial focused build, `Types`, `Primitive`, and the foundation examples
each compiled in approximately 0.3–0.4 seconds. The complete example target
finished in approximately one second after the initial package setup.

Readability finding: the public dependency chain is short. Finite port and
instance identities now use `deriving Enumeration`; constructor declaration
order supplies canonical traversal while generated kernel-checked declarations
hide `nodup` and `ListIndex` transcripts. Tuple fields and module ports share
`SignalMap`; labels make designs readable without affecting structural shape.
Detailed rationale and open questions are recorded in `Design.md`.

## Goal 2A: generic component instances

Introduce the first reusable layer of structural composition without creating
a restricted flat-circuit representation:

- an `EnumeratedMap` shared by signal maps and instance maps;
- the generic relationship from a component identity to its `ModulePorts`;
- canonically ordered symbolic instances of arbitrary components; and
- one named instance of the Boolean `not` primitive.

Do not add endpoints, wiring, composite modules, semantics, or schedules.

Review question: **Can primitives and future composite module identities use
the same component-instance abstraction without replacing it?**

### Goal 2A outcome

This outcome was later simplified by recursive module ownership. `Instances`
is now an `EnumeratedMap ModulePorts`: instance identities retain canonical
ordering, while each value is directly the exact child interface.

The NOT-instance example defines one ordinary label constructor,
`.inverter`, and maps it to `Primitives.not`. Its ports are recovered through
the generic `Instances.ports` operation and `Primitive.ports`. Enumeration is
derived without an author-written classifier or proof term.

The later `ModuleStructure.composite` constructor supplies the child definition at that
interface. The intermediate component vocabulary and external definition-table
idea were removed rather than becoming semantic infrastructure.

The focused complete build finished in approximately two seconds; individual
new files compiled in approximately 0.3 seconds.

## Goal 2B: generic typed endpoints

Define the actual generic source and sink references for a module boundary and
component instances. Exercise them with the named NOT instance, but do not
add wiring or a composite-module record yet.

Review question: **Do endpoint references depend only on component interfaces,
and can a module author select ports by their symbolic labels without casts or
proof transcripts?**

### Goal 2B outcome

Completed with `Silean2/Endpoint.lean`. A `SignalSource` is either a module
input or an instance output; a `SignalSink` is either a module output or an
instance input. Both are indexed by their `SignalType`. Instance endpoints use
only the interfaces in `Instances`, so they do not distinguish primitive from
composite child definitions.

The NOT-instance example typechecks all four endpoint forms using `.value`,
`.inverted`, `.inverter`, `.input`, and `.output`. Thin authoring operations on
`ModulePorts` and `Instances` pin the dependent context before Lean elaborates
those labels. Authors provide the component port function and surrounding
ports/instances explicitly, but require no casts, equality proofs, or tactics.
A later structural owner may make those repeated context arguments implicit;
this goal does not introduce such an owner prematurely.

No negative compiler-message test was retained: it would couple the source to
diagnostic wording. The endpoint result index itself is the compile-time
constraint; a `.bit` endpoint cannot inhabit a vector-indexed endpoint type.

The focused complete build finished in approximately 1.3 seconds, with the new
endpoint and example files each compiling in approximately 0.3 seconds.

## Goal 2C: total typed wiring

Define generic total wiring and the structural module body that owns its
component vocabulary, boundary, instances, and wiring. Describe a complete NOT
wrapper. Do not add semantics or schedules.

Review question: **Does the NOT wrapper read as direct wiring while ensuring
every sink has exactly one type-correct driver?**

### Goal 2C outcome

Completed with `Silean2/Structure.lean`. `Wiring` stores total driver functions
for module outputs and instance inputs, the two possible sink forms. Its
generic `drive` operation combines them. Each result is indexed by the sink's
computed `SignalType`, so shape mismatches cannot be represented. Returning the
same source for more than one sink provides fan-out; no evaluation order is
stored.

`EndpointContext` owns the module boundary ports and canonically ordered
instance interfaces. `ModuleBody` owns that context and its dependent wiring.

The NOT wrapper's two wiring clauses directly state that `.inverter.input` is driven by `.value`
and `.inverted` is driven by `.inverter.output`; executable definitional checks
confirm both assignments. Endpoint expressions use the bound context and only
symbolic endpoint labels, with no casts, equality proofs, tactics, or manual
`SignalType` annotations. The wiring definition uses
ordinary exhaustive pattern matching and no dependent proof transcript.

This structure closely matches a Verilog-like module body: interface,
instances, and complete connectivity. ModuleStructure-definition storage, recursive
reference validation, semantic equations, loop checks, and emission remain
separate later layers.

The focused complete build finished in approximately 1.9 seconds; each new or
changed source file compiled in approximately 0.3–0.4 seconds.

## Goal 2D: scalable enumeration authoring

Replace arity-specific enumeration constructors with one scalable mechanism for
ordinary finite inductive identities. Compare deriving from constructor order
with a general explicit-list construction, test one-, two-, and
three-constructor types, and migrate all declarations if deriving is clearer.

Review question: **Can a designer declare each symbolic identity once while
retaining a canonical, executable, kernel-checked enumeration?**

### Goal 2D outcome

Completed with `Silean2/DeriveEnumeration.lean`. `deriving Enumeration` accepts
any nonempty inductive type whose constructors are all nullary. It generates
`values` in constructor declaration order, a `Nodup` proof, and one constructive
`ListIndex` result per constructor. The generated instance is elaborated and
checked normally by Lean's kernel and requires neither decidable equality nor
author-written proof terms.

A working generic list prototype was also compiled. It required `DecidableEq`,
an explicitly repeated constructor list, its `Nodup` proof, and an exhaustive
coverage proof. Although it scaled computationally beyond pairs, its authoring
transcript still grew with every constructor, so it was rejected.

Unary, binary, and three-constructor examples now all use the same deriving
syntax. Signal labels, tuple labels, instance names, and primitive port labels
as well as the primitive identity vocabulary were migrated.
`Enumeration.singleton`, `Enumeration.pair`, `PairCase`, and all handwritten
arity classifiers were removed.

Incremental builds finished in approximately 3.3 seconds. A full dependency
rebuild after changing the foundational type finished in approximately 4.7
seconds, below the five-second limit.

## Goal 2E: generic authoring cleanup and two-instance validation

Use only broadly reusable cleanup, separate module declarations from API test
fixtures, and define a two-inverter structural body. Evaluate macros from
observed repetition rather than introducing an arity- or primitive-specific
language.

Review question: **Does a second instance add mainly an instance declaration
and connection, and is there enough varied evidence to design a generic macro?**

### Goal 2E outcome

Completed with one new generic operation, `EnumeratedMap.of`. Given any key
type with a derived `Enumeration`, it packages a total value function into an
`EnumeratedMap`. The same operation now constructs primitive port maps, tuple
field maps, signal maps, and instance maps; no specialized wrappers were added.

The actual NOT body lives in `Not.lean`, and individual endpoint fixtures and definitional checks live in
`EndpointChecks.lean`. The NOT declaration is now 47 lines rather than mixing
roughly another 30 lines of endpoint test scaffolding into the module file.

`DoubleNot.lean` is 49 lines. Relative to NOT it adds a second instance name and
one instance-to-instance driver clause; it introduces no framework type, cast,
proof term, tactic, or handwritten signal-type annotation. Checks confirm
canonical instance order and all three connections.

No module or wiring macro was adopted. Both examples repeat port declarations,
body assembly, and dependent endpoint context, but they have the same unary bit
interface and primitive kind. That is insufficient evidence for syntax that
must also handle heterogeneous ports, vectors, tuples, mixed primitive/module
references, and useful missing/duplicate/type errors. Unary-interface builders,
primitive-only builders, and NOT-family helpers were rejected as specialized.
The mux or another heterogeneous structural example should inform any macro.

The focused build after adding all examples finished in approximately 2.2
seconds; focused rechecks finished in approximately 1.2 seconds.

## Goal 2F: structural Boolean mux and authoring review

Build a one-bit mux from NOT, AND, and OR instances using the existing generic
structural representation. Check every driver and fan-out externally, then use
NOT, DoubleNot, and Mux to reassess authoring syntax.

Review question: **Does the representation scale from a uniform chain to a
branched graph with mixed primitive interfaces, and is a macro now justified?**

### Goal 2F outcome

Completed with what is now `Silean2/Modules/BitMux.lean`. Its three inputs, one output, and
four ordered instances directly describe `invertSelect:not`, two AND paths, and
the final OR. The eight exhaustive sink clauses implement the expected graph,
including fan-out of `.select` to the inverter and true-path AND.

`BitMuxChecks.lean` separately confirms instance order, all eight drivers, and the
shared source used for fan-out. The 68-line mux module requires no casts, proof
arguments, tactics, manual signal-type indices, new framework structures, or
module-specific helpers. Compared with the 47-line NOT and 49-line DoubleNot,
growth is predominantly the additional port and instance constructors plus six
additional sink clauses.

The underlying ownership remains suitable: `ModuleBody` packages the boundary,
mixed component vocabulary, instances, and total wiring, while checks and later
semantics remain separate. The structure translates predictably to Verilog:
ports become the module interface, instance-map entries become gate instances,
and each sink-driver clause becomes connectivity. Intermediate gate outputs do
not require handwritten net identities.

No macro was adopted. The mux adds mixed unary/binary interfaces, branching,
and fan-out, so the repeated declaration/wiring shape is now credible. However,
all three modules still use bit signals and primitive references. A general DSL
must also preserve dependent typing and diagnostics for vectors, tuples, and
module-definition references. Recommendation: retain the structural API as the
stable expansion target, proceed with semantics independently, and prototype a
macro only after an aggregate or hierarchical structural example supplies that
remaining evidence.

The focused mux build finished in approximately 1.6 seconds; subsequent full
rechecks finished in under one second.

## Architecture checkpoint after Goal 2F

The Silean-informed review is recorded in `ArchitectureCheckpoint.md`. Its main
finding is that the local typed netlist is promising, but hierarchy ownership
must be settled before structural nodes and equations are made foundational.
At that checkpoint the examples did not exercise hierarchy, partial-output
dependencies, state, aggregates, or parameterized instance families.

## Concrete target architecture

The plan is concrete but deliberately revisable:

1. `ModulePorts` contains only inputs and outputs used for connectivity. A
   primitive explicitly declares local stored state; `ModuleStructure.structuralState`
   recursively derives a composite's instance-labelled state from its actual
   child modules.
2. `ModuleCycleContract` separately owns abstract behavioral state. It need not have
   the same shape as structural state; combinational contracts use the
   canonical empty state map.
3. A complete structural module recursively owns its body and one correctly
   typed child definition for every instance. Contracts are separate objects.
4. Primitive equations induce an order-independent one-cycle `IsSolution`
   relation over recursively exposed primitive occurrences. It does not consult
   contract rules or prescribe an evaluation order.
5. Hierarchically composable structural rules expose precise per-output
   dependencies. A complete availability-ordered rule derivation proves any
   two satisfying `ProposedValues` are equal. This positive evidence replaces
   a standalone acyclicity predicate unless one is later needed.
6. Schedules use a valid structural-rule order to construct one
   `ProposedValues` and prove it satisfies `ModuleStructure.IsSolution`. Uniqueness is
   established separately from schedule execution; no public `ModuleStructure.evaluate`
   is required for contract correctness.
7. Contract correctness is trace inclusion: for every structural execution and
   input sequence, there exists a temporally coherent contract execution with
   the same outputs. Successive witnessed contract states must obey the
   contract state rule.
8. Contract-to-structural state correspondences, invariants, and schedules are
   proof witnesses. A composite correspondence will often decompose parent
   contract state into child contract states and reuse child correspondences.
   Correspondences may be relations and need no injectivity, surjectivity, or
   round-trip laws unless a particular proof needs them.
9. Naming and shallow Verilog rendering consume structural definitions;
   neither contracts nor proof certificates determine emitted structure.

This state correction is complete. Composite structural state is derived from
the actual child modules instead of stored in ports or connected by a
parent-to-child `StateConnections` map. Contract state is independently owned,
and contracts are not fields of `ModuleStructure`.
The partially attempted structural `StateOwnership` bijection remains rejected
because canonical hierarchy-shaped state makes it redundant.

## Next goal: uniform signatures and rule-based contracts

Migrate the foundation to the single stateful model and add the contract
language before adding module evaluation:

- add a state `SignalMap` to `ModulePorts` and a state shape to
  `ModuleSignature`;
- provide one canonical empty state map and migrate NOT, DoubleNot, and Mux to
  it without creating combinational-specific wrappers;
- define output rules with exact input-read and output-write selections;
- define one total next-state rule for every contract;
- define `ModuleCycleContract` with finite rule identity and output
  coverage/non-overlap;
- record the relational shape of `Implements`, while deferring its Lean
  definition until structural `Solution` exists; and
- exercise two independent rules with a contract for a `DualNot`-shaped
  interface, without yet building its hierarchy.

Do not add module evaluation, structural equations, schedules, hierarchy,
storage primitives, or refinement proofs. Empty state must fall out of the
uniform definitions rather than require a parallel API.

Review question: **Can the same signature and contract types describe mux,
`DualNot`, and a future enabled register while retaining precise per-output
dependencies?**

### Goal outcome

Completed with one uniform state-bearing foundation. `ModulePorts` now contains
input, state, and output `SignalMap`s, and `ModuleSignature` contains their
anonymous shapes. `emptySignalMap` and its unique valuation are used by all
current Boolean primitives and structural examples; no combinational-specific
module, signature, contract, or state-rule API was introduced.

`Silean2/ModuleCycleContract.lean` adds typed `SignalSelection`, dependency-aware
`CycleOutputRule`, total `CycleStateRule`, and `ModuleCycleContract`. A contract's finite rule
catalogue must flatten to a permutation of the canonical output labels. Generic
theorems derive output coverage and global write non-overlap from that single
condition.

The Mux contract has one three-input/one-output rule. The DualNot-shaped
contract has two independent one-input/one-output rules. Checks confirm their
selections, results, empty state, and written-output order. Rule authoring uses
generic map-bound `select`/`prepend` operations and symbolic labels; it contains
no positional references, casts, or module-specific helper machinery.

Enabled-register fit: its output rule can return current state without reading
an input, and its total state rule can select input versus current state using
enable. FIFO fit: forward and ready can remain separate rules with distinct
input selections, while one state rule sees all handshake inputs. Structural
storage ownership and evaluation remain deliberately unimplemented.

Review result: the same contract representation covers grouped mux behavior,
independent DualNot outputs, future nonempty state, and FIFO dependency
patterns. The next uncertainty is module-definition ownership.

## Goal: recursively owned hierarchical modules

Add a complete `ModuleStructure` whose composite constructor owns its local body,
contract, and one correctly typed child module for every instance. Remove the
external component/module-identifier scaffolding. Validate reusable definitions
and distinct occurrences with hierarchical DualNot and a parent containing two
instances. Add only the minimal typed path vocabulary; do not add equations,
evaluation, schedules, correctness propositions, storage, naming, or emission.

Review question: **Does every instance intrinsically own a correctly typed
reusable definition while recursive paths distinguish its hardware
occurrences?**

### Goal outcome

Completed with `Silean2/ModuleStructure.lean`. `ModuleStructure.primitive` identifies a closed
leaf. `ModuleStructure.composite` owns a `ModuleBody` and
`childStructure name : ModuleStructure (instances.ports name)`. Missing implementations and
port mismatches are therefore unrepresentable without a definition environment
or lookup proof. Contracts were subsequently removed from `ModuleStructure` during the
foundation ownership cleanup.

Instances now map names directly to required `ModulePorts`. `ComponentRef`,
`ComponentPorts`, `ModuleId`, and the empty example component vocabulary were
removed. Endpoints and wiring became smaller because they need only the stored
instance interfaces.

HierarchicalDualNot owns two primitive NOT definitions. RepeatedDualNot returns
the same HierarchicalDualNot module value for both child names, demonstrating
definition reuse. `ModulePath` distinguishes `.first/.forwardNot` from
`.second/.forwardNot`, and `PrimitiveOutputOccurrence` retains the typed leaf
output at each occurrence. No structural meaning is attached to these paths.

NOT, DoubleNot, and Mux now also have complete module assemblies in separate
small files. Primitive contracts remain separate public behavioral rules, not
fields of primitive modules and not primitive structural equations.

Review result: recursive ownership is concise and proof-oriented. Definition
sharing is reuse of the same child module value; occurrence identity comes from
the path followed through instance names. Stable definition keys remain solely
a later naming/emission concern.

## Validated milestones and remaining pressure tests

1. Contract-free modules, recursively derived structural state, and separate
   contract state — complete.
2. Order-independent one-cycle equations over recursively exposed primitive
   occurrences — complete.
3. Compositional structural rules and uniqueness — complete. Complete
   availability-ordered rule application makes satisfying proposals unique;
   reusable parent rules are obtained by applying child rules through wiring.
4. Schedules as generic constructive evaluators — complete. Schedule execution
   constructs satisfying proposals; existence plus the separate uniqueness
   theorem gives exactly one same-cycle solution.
5. Order-independent behavioral contract steps and a derived unique executable
   result — complete.
6. Relate abstract contract state to structural state and prove one-cycle
   refinement for Mux, DualNot, and EnabledRegister — complete.
7. Foundation/API review and documentation tidy — complete.
8. Bit-level FIFO structure, state correspondence, uniqueness, and contract
   refinement — complete, but it did not exercise use of the FIFO as a child
   through separate forward and ready dependencies.
9. Rule-local certified hierarchy pressure test — next. Recover the original
   false-whole-instance-cycle case and determine whether structural dependency
   rules can be derived generically from certified contract rules.
10. Correct the primitive/rendering boundary and reconcile its documentation.
11. Native aggregates, `Fin`-indexed families, and generic data-bearing Mux,
    EnabledRegister, and FIFO modules.
12. Generic hierarchical refinement composition, extracted only from evidence
    in the generalized modules.
13. Naming, shared-definition collection, and shallow Verilog rendering.
14. Optional trace packaging or other proof conveniences only when a consumer
    needs them.

## Current checkpoint

Goal 2F and the later foundation corrections are complete. Recursive hierarchy,
canonical structural state, separate contracts, and order-independent
one-cycle structural meaning now exist. Availability schedules construct
satisfying proposals and, together with the separate uniqueness theorem, prove
exactly one same-cycle solution. One-cycle contract refinement now exists;
there is still no trace semantics, lowering, naming, or rendering.

## Goal outcome: clean contract-free structural hierarchy

The initial implementation used `ModuleBoundary`, state-bearing `ModulePorts`,
and `Instances.structuralState`. The subsequent foundation review removed that
duplication. `ModulePorts` now owns only inputs and outputs. Primitive leaves
explicitly choose `Primitive.localState`, while `ModuleStructure.structuralState`
recursively builds a labelled `StructuralState.children` branch from the actual
child modules. A composite author supplies no parent state or state mapping.

`ModuleCycleContract` is indexed by connectivity-only `ModulePorts` and owns an
independent contract-state map. Its output and transition rules use that state,
never the implementation's structural state. Contracts are not stored in
`ModuleStructure`; primitive contracts are also separate values.

Hierarchy checks show that `RepeatedDualNot` has distinct `.first` and
`.second` structural-state branches and that each contains the recursively
derived `HierarchicalDualNot` state. Its separately declared contract state is
empty.

## Goal outcome: order-independent one-cycle structural meaning

`StructuralState.Values` preserves labels recursively, and `ModuleStructure.State`
specializes it to a complete module. `ProposedValues` stores only stable output
interfaces at every occurrence, primitive next-local-state values, and child
proposals. Instance inputs, child current states, and composite next state are
derived rather than duplicated.

`Primitive.IsSolution` defines leaf equations without importing or consulting
contracts. `ModuleStructure.IsSolution` recursively checks child proposals with inputs
derived through `Wiring`, selects current child state by instance label, and
requires every composite boundary output to equal its wired source. The
definition is a conjunction of equations and universal child obligations; it
contains no schedule or evaluation order.

Focused checks cover equality, NOT, Mux, HierarchicalDualNot, and
RepeatedDualNot. An invalid NOT proposal satisfies its boundary alias but is
rejected by the primitive equation, and the repeated-hierarchy check confirms
that its next state is recursively assembled from leaf proposals.

## Goal outcome: single-bit storage and EnabledRegister

`Primitives.register` is a nullary, single-bit primitive and remains part of the
finite `Primitive` enumeration. Its input is the proposed next bit, its output
is the current bit, and `Primitive.localState` owns one `.stored` bit. No
generic or signal-type-parameterized primitive family was introduced.

Primitive output equations now receive current local state, and the separate
`Primitive.NextStateSatisfy` relation handles transitions. Combinational leaves
preserve empty state; the register requires output equal to current `.stored`
and next `.stored` equal to `.input`.

## Goal outcome: compositional structural uniqueness

`StructuralRule` states which boundary inputs determine which outputs among
arbitrary satisfying proposals at one current state. It is independent of
behavioral contract rules. `StructuralSchedule` is an availability certificate: it
stores child rule applications and proofs that their wired reads are already
available, but stores neither values nor positional references.

`StructuralSchedule.finishAgreement` proves by schedule induction that two satisfying
proposals agree on every output made available. A complete schedule plus child
at-most-one proofs yields `ModuleStructure.composite_hasAtMostOneSolution`; no negative acyclicity
predicate is required. `ModuleStructure.composite_fullRule` and
`ModuleStructure.composite_structuralRule` lift this reasoning into reusable parent
rules.

The examples prove uniqueness for NOT, Mux, HierarchicalDualNot,
RepeatedDualNot, and EnabledRegister. RepeatedDualNot applies the reusable
hierarchical rule twice. EnabledRegister applies the state-only register output
rule before the reusable mux rule, demonstrating that legal state-broken
feedback is accepted. The focused rule-check build completes in under two
seconds on the current workspace.

EnabledRegister structurally composes the existing Mux module with one register
leaf. Ordinary wiring feeds the register output into the mux hold input and the
mux result into the register input. Its structural state is automatically a
`.selection` branch containing the Mux hierarchy and a `.storage` branch
containing the register bit.

Focused checks prove hold and update proposals, confirm their different derived
next states, and reject an incorrect current output and an incorrect next state
through the same generic `ModuleStructure.IsSolution` relation.

## Goal outcome: constructive schedule evaluators and existence

`ExecutableStructuralRule` augments a semantic `StructuralRule` with a program,
a proof that only declared reads affect declared writes, and a proof that its
written values agree with any satisfying proposal. Primitive programs are
defined once; a proved `StructuralEvaluator` can expose any structural rule as an
executable rule for its parent.

`StructuralSchedule.execute` operates on a generic typed child-output store. The
canonical defaults merely initialize the total Lean functions; availability
proofs prevent them from being read. Rule writes must be fresh, which makes
the scheduled store monotone on already available outputs. The generic replay
proof relates the final store to child evaluator proposals and proves
the evaluator returned by `StructuralEvaluator.composite` satisfies
`ModuleStructure.IsSolution`.

`ModuleStructure.HasExactlyOneSolution` combines an evaluator with the earlier at-most-one
theorem. NOT, Mux, and EnabledRegister have executable evaluators and exactly-one
theorems. Concrete checks evaluate NOT and Mux and verify EnabledRegister hold,
update, current output, and next-state behavior. The register output program
reads no same-cycle input, so its scheduled value makes the mux hold path
available before the mux is executed. A focused rebuild of the evaluator checks
completed in approximately 4.5 seconds, and the full cached package build in
approximately 2.7 seconds.

## Goal outcome: order-independent contract steps

`ModuleCycleContract.OutputRulesHold` requires every behavioral output rule to agree
with complete output values; `ModuleCycleContract.EvaluatesTo` additionally fixes
next contract state to the total state rule. These relations contain no rule
order. Exact write coverage generically proves that each input/current-state
pair has exactly one output/next-state result.

Private typed assignments bridge rule targets to complete valuations.
`applyOutputRules` folds their disjoint writes and `evaluate` pairs the result
with the state rule; generic proofs establish agreement and uniqueness. Mux,
two-rule DualNot, and stateful EnabledRegister all use this machinery. The
focused contract-semantics check built in approximately 1.4 seconds.

## Goal outcome: one-cycle structural refinement

`Implements` relates independent contract state to recursively derived
structural state. For every corresponding pair of current states and every
satisfying structural proposal, it requires a `ModuleCycleContract.EvaluatesTo`
result with the same boundary outputs and a next contract state corresponding
to the proposal's next structural state. It does not depend on a chosen
schedule, evaluator, or uniqueness theorem.

Mux and hierarchical DualNot prove refinement with trivial empty-state
correspondences. EnabledRegister relates the abstract `.stored` bit to the
structural `.storage/.stored` bit and proves both hold and update preservation.
Its proof manually reuses the Mux refinement for the selection child, giving a
concrete basis for later generic hierarchical composition without adding it
yet.

Review result: the relational contract semantics materially simplifies the
statement of refinement. Contract output assembly is merely deterministic rule
application, exposed as `applyOutputRules`; the combined operation is
`evaluate`, and the relation is `EvaluatesTo`. Structural
evaluator and uniqueness machinery correctly remained irrelevant to the proof,
which covers every structural solution. The focused refinement build completes
in approximately 1.5 seconds.

## Goal outcome: connected-foundation tidy

The public contract surface now consists of rule agreement
(`CycleOutputRule.Holds` and `OutputRulesHold`), relational evaluation
(`EvaluatesTo`), deterministic output assembly (`applyOutputRules`), combined
`evaluate`, and their agreement/uniqueness theorems. Heterogeneous assignments,
folds, and their preservation proofs are private implementation details. The
redundant `nextState` wrapper and an always-provable exactly-one-contract record
were removed.

Structural uniqueness terminology now distinguishes
`HasAtMostOneSolution` from `HasExactlyOneSolution`. The unused standalone
`HasSolution` wrapper was removed; `StructuralEvaluator` itself is constructive
existence evidence. `StructuralRules.lean` remains the semantic certificate/at-most-one
layer and `StructuralEvaluation.lean` remains executable construction/replay. Their long
generic inductive proofs do not become clearer when split across more files.

The structural description is now explicitly named `ModuleStructure`;
one-cycle behavior is `ModuleCycleContract`; and the only
bundle is `ModuleCycleCertified`. That bundle contains the structure, cycle
contract, state correspondence, `Implements` proof, and evidence that every
structural state has a corresponding contract state. Mux, DualNot, and
EnabledRegister now export certified values. Structural execution terminology
is `StructuralEvaluator`/`evaluate`, not solving, and signal assignments use
the direct name `Values` rather than logic-oriented valuation terminology.

The refinement examples retain private, local normalization lemmas where Lean
must expose a concrete rule target, but add no module-specific public helper
API. Their remaining detail follows actual gates and wires. The canonical
current overview is now `ArchitectureCheckpoint.md`; this roadmap is explicitly
historical, so superseded goal outcomes no longer masquerade as the current
design.

## Goal outcome: concrete design organization

Concrete primitives are no longer constructors of a closed `Primitive`
enumeration. `Primitive` is now the generic leaf-description record, while
Not, And, Or, Eq, and Register are independent single-bit values. Each lives
with its cycle contract in one file under `Silean2/Primitives/`; shared port
shapes alone live in `PrimitivePorts.lean`.

Reusable Mux and EnabledRegister designs each live in one file under
`Silean2/Modules/`. Test-only Not, DoubleNot, DualNot, HierarchicalDualNot, and
RepeatedDualNot fixtures remain under `Silean2/Examples/`, also consolidated to
one file per fixture. The `Modules` import surface therefore contains useful
designs rather than verification scaffolding.

## Goal outcome: one-entry FIFO structure and contract

The old bit-level fall-through FIFO has been reconstructed as two reusable
files. `Modules/FifoControl.lean` contains the three-primitive readiness/update
control block. `Modules/OneEntryFifo.lean` contains the five-child FIFO hierarchy
and its independent two-bit cycle contract.

Both modules now keep their execution and correctness evidence beside the
useful structure. Each has a dependency-ordered complete schedule, evaluator,
structural uniqueness proof, contract refinement proof, and exported
`ModuleCycleCertified` value. The FIFO refinement composes the certified
EnabledRegister, FifoControl, and Mux children instead of re-proving their
behavior from flattened equations. Executable checks cover empty fall-through,
capture into empty storage, full backpressure/hold, and simultaneous
dequeue/replacement. Focused compilation remains below the five-second budget.

## Architecture review after the bit-level FIFO

The repository-wide comparison in `ArchitectureReview.md` supersedes the
earlier conclusion that the connected foundation is ready to proceed directly
to more modules or rendering.

The review confirms that Silean 2's independent structural solution relation,
explicit existence and uniqueness, recursively derived structural state, and
refinement over arbitrary solutions are improvements over the old packaging.
It also identifies four unresolved foundation issues:

1. The generic machinery supports partial structural rules, including an
   executable `respectsReads` guarantee, but useful certified modules do not
   systematically expose one structural dependency view per contract rule.
2. The old bidirectionally connected partial-output regression, which rejects
   false whole-instance cycles, has not been reconstructed in Silean 2.
3. The concrete Mux, EnabledRegister, and FIFO data paths are bit-specific even
   though the type foundation supports vectors and tuples.
4. `Primitive` is now an open semantic record, conflicting with the older
   closed/renderable primitive boundary and with parts of the current design
   documentation.

The FIFO proof also contains enough repeated wiring, child-proposal, boundary,
and state-correspondence transport to justify testing generic hierarchical
refinement laws. Those laws must be derived from representative modules rather
than introduced as FIFO-specific helpers.

## Goal outcome: certified rule-local hierarchy foundation

Each named output rule of a `ModuleCycleCertified` value now generically induces
a semantic `StructuralRule` with the same declared reads and writes. The proof
uses only `hasCorrespondingState` and `Implements`; it does not inspect the child
structure's implementation or evaluation construction.

The new `Certified.Schedule` calls a named contract rule from a family of
certified children. A parent provides one schedule for each output rule and one
state schedule. Generic combination replays them while omitting rules already
called; its coverage condition requires every immediate child contract rule to
be exercised. The resulting theorem proves parent structural uniqueness using
only derived child rules and child certificate uniqueness.

The bidirectional DualNot regression validates the design. Its forward cone
calls `a.forward` then `b.forward`; its backward cone calls `b.backward` then
`a.backward`. A separate theorem proves that neither child could start if both
directions were collapsed into one whole-child dependency summary. Thus the
test distinguishes the correct rule-local interface from the regressed one.

The parent proof additionally establishes a satisfying structural proposal,
at-most-one solution, exactly one solution, and refinement to its independent
two-rule identity contract. It uses only certified child existence and
refinement, not child evaluators or internal schedules. The parent itself is
exported as `ModuleCycleCertified`.

`ModuleCycleCertified` now stores propositional structural existence and
uniqueness in addition to structure, contract, state correspondence/coverage,
and `Implements`. It stores no schedule or evaluator. These two fields yield a
generic exactly-one theorem while keeping `ModuleStructure.IsSolution` as the
only structural meaning.

Architectural decision: adopt generic certified-rule derivation and named child
contract calls as the normal hierarchical interface. `StructuralRule` remains
the useful semantic dependency theorem. `ExecutableStructuralRule` and
`StructuralEvaluator` are unnecessary on this new path. BitMux and the complete
useful dependency chain through EnabledRegister, FifoControl, and OneEntryFifo
have now been migrated away from them.

Focused builds of the new scheduling foundation and regression remain below
five seconds; the final bidirectional target builds in about 1.3 seconds. No
`sorry`, `admit`, `Classical.choice`, or `native_decide` is present in the new
files.

## Corrective plan before evaluator removal (now superseded)

After the completed rule-local correction, proceed in small reviewed goals:

1. Review and isolate or remove the remaining legacy evaluator-oriented API;
   no useful module in the BitMux/Register/FIFO chain now depends on it.
2. Decide and implement the primitive identity/rendering boundary, then correct
   stale documentation.
3. Generalize BitMux and EnabledRegister data over `SignalType`, exercising vector
   and named-tuple shapes without adding generic primitives.
4. Generalize OneEntryFifo data using those modules while retaining bit-valued
   handshake control.
5. Extract generic boundary-output and next-state correspondence
   composition laws demonstrated by the generalized proof.
6. Reassess the certified-module bundle, file responsibilities, terminology,
   and proof size before resuming naming or Verilog work.

## Goal outcome: removal of the legacy structural evaluator

The evaluator-oriented structural path has been removed. The audit found one
remaining dependency in the old HierarchicalDualNot certification: its
uniqueness proof came from `StructuralRuleChecks`. HierarchicalDualNot now uses
certified NOT children, rule-local output schedules, a state schedule, generic
child-rule coverage, and the generic certified-schedule uniqueness theorem.
Its constructive existence proof uses child certificate existence directly.

With that dependency migrated, `StructuralRules.lean`,
`StructuralEvaluation.lean`, and their two dedicated check files had no current
semantic or module consumers and were deleted. The aggregate imports no longer
publish them.

The remaining layers have distinct responsibilities:

1. `StructuralSemantics` defines the order-independent structural equations.
2. `StructuralDependency` defines semantic rule dependency and at-most-one
   solution propositions.
3. `CertifiedSchedule` provides named child-contract schedules solely as
   positive availability evidence for uniqueness.
4. `ModuleCycleCertified` carries propositional structural existence and
   uniqueness together with behavioral refinement.
5. `ModuleCycleEvaluation` evaluates behavioral contract rules and is not a
   structural solver.

No public object selects a structural result. Exactly-one results are proved by
combining certificate existence with schedule-derived uniqueness. The full
library and example aggregates build below five seconds on the current
workspace.

## Following goals after evaluator removal

1. Decide and implement the primitive identity/rendering boundary, correcting
   the remaining stale primitive documentation.
2. Review the generic OneEntryFifo result and extract only genuinely reusable
   boundary-output or next-state correspondence laws demonstrated by it.
3. Reassess the certified-module API and proof organization before resuming
   Verilog-oriented work.

## Goal outcome: recursively certified generic register

The generic register is now defined and certified for every `SignalType`.
Its bit case is exactly the closed single-bit register primitive. Vector and
named-tuple cases instantiate a splitter, one recursively certified register
per immediate component, and a combiner. Nested aggregates therefore recurse
until all physical storage is owned by bit-register leaves; no aggregate
primitive was introduced.

The public behavioral contract remains one register contract over the original
aggregate signal: the current aggregate state is observed at the output and the
aggregate input becomes next state. Its refinement relation decomposes that
contract state through the splitter and reuses each component register's state
correspondence. Split/combine inverse laws prove both state coverage and
reassembly of component outputs.

Two generic finite-family mechanisms support the proof. `Enumeration.exists_pi`
constructively assembles dependent witnesses for all enumerated children without
`Classical.choice`. `Certified.Schedule.callFamily` schedules a finite family
of distinct child rules whose reads are initially available, proving both exact
membership and coverage without making enumeration order semantically
significant. The register uses it for all component `observe` rules, followed
by the combiner; its state schedule exercises the splitter. Generic schedule
coverage then proves structural uniqueness.

Vector and nested named-tuple checks establish structural existence and exact
uniqueness through the exported certificate. Focused compilation remains below
five seconds: the generic register compiles in about 2.1 seconds and its check
file in under one second on the current workspace.

This validates recursive structural aggregation as the preferred direction.
The next module-level step is a generic mux using the same splitter/component/
combiner shape, followed by a generic enabled register composed from the
generic mux and this register.

## Goal outcome: generic leafwise logic and mux

Generic `Mask`, `BitwiseOr`, and `Mux` modules are now structurally defined and
certified for every `SignalType` without adding aggregate primitives.

- `Mask(T, bit) → T` uses the existing AND primitive at bit leaves. Vectors
  and tuples split the value, recursively mask every immediate component while
  broadcasting the one-bit mask, then combine the results.
- `BitwiseOr(T, T) → T` uses the existing OR primitive at bit leaves.
  Aggregate cases split both operands, recursively combine corresponding
  components, then reassemble the result.
- `Mux(T, T, bit) → T` is a shallow hierarchy containing NOT, two certified
  generic Masks, and one certified generic BitwiseOr. Its correctness proof
  uses those child contracts rather than reopening their recursive structures.

`SignalLogic` contains only reusable value semantics and splitter decomposition
laws. The Boolean mask/OR identity needed specifically to certify Mux remains a
private theorem in `Modules/Mux.lean`.

The shared scheduling addition is `Certified.Schedule.callFamilyAfter`: it
schedules an arbitrary finite injective family after a supplied availability
prefix while preserving that prefix and proving exact final membership. Mask
uses it after one splitter; BitwiseOr uses it after two splitters. A generic
`Enumeration.sum` supports the latter topology without a module-specific finite
enumeration proof.

All three modules prove structural existence, schedule-derived uniqueness,
trivial empty-state correspondence, and behavioral contract equivalence.
Focused checks cover a bit Mask, vector BitwiseOr, and nested tuple Mux through
their public exactly-one result theorems. Cached focused builds are below five
seconds (`Mask` about 2.3s, `BitwiseOr` about 2.1s, `Mux` about 1.6s, and the
combined check file below one second on the current workspace).

The next data-path step is to migrate `EnabledRegister` from `BitMux` to the
generic Mux and generalize its stored data over `SignalType`. The FIFO data path
can follow once that dependency is certified.

## Goal outcome: generic EnabledRegister

`EnabledRegister` is now generic over every `SignalType`. Its external enable
remains one bit; input, output, and independent contract state all have type
`T`. Structurally it contains exactly two certified children: generic `Mux T`
selects the held or incoming value, and generic `Register T` owns the state.
No aggregate primitive or parallel specialized implementation was added.

The output schedule calls the Register's input-independent `observe` rule. The
state schedule calls that same rule before Mux, making the held value available
to selection. Generic child-rule coverage therefore proves structural
uniqueness with the existing scheduling machinery.

Structural existence no longer inspects a concrete `.storage/.stored` leaf.
It obtains a current aggregate contract state from the Register certificate,
constructs Mux and Register proposals, and uses Register refinement to prove
that the proposed storage output is the held aggregate value. The parent state
correspondence delegates directly to the Register child's recursive state
correspondence. Refinement then reuses both child certificates to prove output,
conditional update, and preservation of next-state correspondence.

At this checkpoint the FIFO remained intentionally bit-specific and instantiated
`EnabledRegister .bit`. Its proof migration removed direct access to
EnabledRegister's former primitive storage state; FIFO existence, refinement,
and state coverage use the child certificate instead. The following goal then
generalized its payload independently.

Focused public-certificate checks cover bit hold/update, a three-bit vector,
and a nested tuple, including existence of a corresponding aggregate contract
state. Contract evaluation checks still cover the bit hold and update cases.
Focused compilation remains below five seconds: EnabledRegister builds in about
1.7 seconds when rebuilt as a dependency, its checks in under one second, and
the migrated FIFO in about 3.6 seconds on the current workspace.

## Goal outcome: generic OneEntryFifo

`OneEntryFifo` is now generic over every payload `SignalType`. Validity,
readiness, and the storage-update condition remain single bits. The data input,
data output, and stored-data contract state have type `T`.

The hierarchy retains five children: `EnabledRegister .bit` stores validity,
`EnabledRegister T` stores the payload, `FifoControl` computes handshake
control, the OR primitive computes output validity, and `Mux T` selects between
fall-through input data and stored data. No aggregate FIFO primitive or
shape-specific FIFO implementation was introduced.

The two contract output rules remain independent: `forward` determines output
validity and payload, while `ready` determines upstream readiness. Their
structural schedules, together with the single state schedule and child-rule
coverage, prove uniqueness. Structural existence obtains abstract current
values from both EnabledRegister certificates and constructs child proposals
without inspecting either register's recursive state tree.

State correspondence separately delegates stored validity to
`EnabledRegister .bit` and stored payload to `EnabledRegister T`. The refinement
proof reuses the EnabledRegister, FifoControl, Mux, and primitive certificates
to establish both output rules and transport the contract's next state back to
the two child structural states. The Mux contract characterization theorem is
public so parent modules can use its behavioral equation without exposing its
wiring or schedules.

Checks retain all bit-valued FIFO cases and add vector fall-through/capture plus
nested-tuple simultaneous replacement. Vector and nested-tuple checks also use
the public certificate to establish exactly one structural result, and the
nested check exercises corresponding-state existence. Focused builds remain
below five seconds: the FIFO builds in about 3.5 seconds and its checks in about
1.1 seconds on the current workspace.

## Current review: certified child composition

Reviewing Mux, EnabledRegister, and OneEntryFifo identified one repeated law
that is genuinely independent of module wiring and behavior: if a composite
proposal satisfies the parent structure and a child contract state corresponds
to that child's structural state, then the child certificate evaluates its
automatically wired inputs and preserves correspondence for the proposed child
next state.

`CertifiedComposition` now owns the certified-child collection, the derived
child and composite structures, and this `childImplements` theorem.
`CertifiedSchedule` imports that layer and remains concerned only with positive
dependency schedules and uniqueness. Mux, EnabledRegister, and OneEntryFifo use
the generic theorem instead of manually extracting and passing each child's
solution proof.

This review deliberately did not abstract module-specific wiring equalities or
contract-specific next-state transport. Those remain the actual local proof
obligations. Public contract characterization theorems were added or exposed
for NOT, OR, FifoControl, Mux, and OneEntryFifo so parent proofs can use child
behavior without unfolding child structures, wiring, or schedules.

## Goal outcome: computable module structures and opaque certification

All reusable modules now expose their `moduleStructure` as a standalone
computable definition. Recursive Register, Mask, and BitwiseOr structures are
defined directly by signal shape. Mux, EnabledRegister, and OneEntryFifo define
their composite child-structure maps directly from those public child
structures. BitMux and FifoControl were audited to the same boundary.

`ModuleCycleCertification structure contract` is the shared proof-only record.
It is indexed by the exact public structure rather than owning a second
structure. Generic structure and contract transport move the entire dependent
certificate across a proved identity at one boundary. Each module keeps its
certification implementation opaque/noncomputable and bundles it as
`ModuleCycleCertified` only for behavioral composition. Therefore a backend
can inspect public structures without evaluating certification; the direct
FIRRTL renderer now does exactly that.

The migration also tightened the parent interface: OneEntryFifo now expresses
its state relation through its child certificates rather than referring to
EnabledRegister's proof-internal state correspondence. Existing public
contract characterization theorems and `Certified.childImplements` remain the
composition API.

## Goal outcome: direct FIRRTL generation

The public computable `ModuleStructure` hierarchy now has a direct executable
FIRRTL consumer. `ModuleNaming` is indexed by the exact source structure and
adds only readable module, port, instance, state, and recursive child names.
Generic traversal collects occurrences, shared definitions, ports, instances,
and typed connections without evaluating certification or constructing a
lowered semantic circuit.

`FIRRTL.renderCircuit` emits FIRRTL 4.0 text for all current structural cases:
the supported single-bit NOT, AND, OR, equality, and register primitives;
vector/tuple splitters and combiners; and arbitrary composites. It uses direct
connects rather than inventing intermediate wires. Executable validation
diagnoses illegal or duplicate local identifiers, module-name collisions, and
one module key being assigned different rendered definitions.

A backend-only `clock` input is added uniformly to every module and propagated
to every child instance. The register primitive declares a reset-free FIRRTL
register on that clock; clock remains absent from ordinary `ModulePorts`.

Readable naming covers BitMux, recursive generic Register, Mask, BitwiseOr,
Mux, EnabledRegister, FifoControl, and OneEntryFifo. Executable checks render a
complete BitMux, vector Register, tuple EnabledRegister, and vector-payload
OneEntryFifo and inspect hierarchy, aggregate types, operations, register
declarations, direct connections, and clock propagation. The syntax was
reviewed against the local FIRRTL 4.0 specification; no local FIRRTL parser was
available. Focused cached builds remain below five seconds, with the FIRRTL
check target itself under one second.

## Goal outcome: executable bit-register toolchain check

A pinned Nix development shell now provides the complete external toolchain:
the project-selected Lean version through Elan, CIRCT `firtool`, Verilator,
Make, Python, cocotb, and pytest. This replaces ambient tool assumptions and
keeps Python packages pinned transitively by `flake.lock`.

`FIRRTL.emitMain` is the small shared executable boundary. Each concrete design
configuration owns a dedicated Lean executable; the first is
`emit-bit-register`. It emits to stdout or an explicit `--output PATH` and does
not encode hardware configuration in command-line strings.

The top-level Makefile exposes separate `firrtl-bit-register`,
`verilog-bit-register`, and `test-bit-register` stages, with every generated
artifact below `build/bit-register`. CIRCT successfully parses the generated
FIRRTL and produces SystemVerilog containing the expected positive-edge
register. Verilator 5.050 and cocotb 2.0.1 compile and simulate it.

The cocotb test follows the existing Zamlet convention: a standard cocotb
`Clock` runs continuously, and a drive phase waits for `RisingEdge` followed by
`FallingEdge`. It avoids assumptions about initial register contents, then
checks five cycles of between-edge stability and rising-edge capture. The clean
end-to-end run passes; cached FIRRTL and SystemVerilog targets take about 1.4
seconds including Nix shell startup, and the cached simulation takes about 2.1
seconds.

The same pipeline now exercises a generic one-entry FIFO carrying a nested
tuple/vector payload. Recursive field labels are layered onto the computable
structure by FIRRTL naming metadata and propagated through every generic child
and split/combine adapter. CIRCT accepts the resulting named aggregate types,
and cocotb verifies all eight flattened payload leaves across fall-through,
capture, backpressure, simultaneous replacement, and dequeue.
