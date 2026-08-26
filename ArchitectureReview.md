# Silean 2 architecture review

Date: 2026-08-25

Status update (2026-08-26): the corrective bidirectional rule-local review
described below has now been completed. The final section records its result;
earlier recommendations are retained as the evidence that motivated it.

## Purpose

This review compares the original `silean` architecture with the current
`silean2` experiment. It evaluates whether the new foundation preserves the
important guarantees already established by the original project while making
the structural meaning and proof chain cleaner.

The review covers the design history, foundational definitions, hierarchy,
rule and schedule machinery, structural semantics, evaluators, contracts,
certification, representative modules, and regression tests in both projects.
It does not treat compilation or the presence of proofs as evidence that the
chosen abstractions are appropriate.

No implementation changes were made as part of this review.

## Executive conclusion

Silean 2 has a better semantic center, but it has not yet preserved every
important modular interface and regression test from Silean.

Keep these Silean 2 improvements:

- a contract-free `ModuleStructure` containing only hierarchy and wiring;
- recursively derived structural state;
- an order-independent `ModuleStructure.IsSolution` relation;
- explicit existence and uniqueness results;
- independent abstract contract state related by `stateCorresponds`; and
- `Implements`, which quantifies over every satisfying structural proposal.

Correct these issues before extending the module library:

1. Restore precise rule-local hierarchical evaluation as a systematic reusable
   interface, and test it with the old false-whole-instance-cycle example.
2. Generalize data-bearing Mux, EnabledRegister, and FIFO modules over
   `SignalType`.
3. Restore a closed or otherwise explicitly renderable primitive boundary.
4. Add generic hierarchical refinement and state-correspondence laws so useful
   module proofs do not manually normalize every wire and child proposal.
5. Clarify the ownership and naming of structural dependency, schedule,
   uniqueness, and evaluation machinery.

The desired direction is not a return to the old packaging. It is to retain the
new independent structural semantics while recovering the old design's precise
rule-local modularity.

## What the original Silean established

### Structure, behavior, and certificates

The original project eventually distinguished these roles:

- typed ports, child instances, wiring, primitive identities, and state
  ownership described hardware structure;
- `ModuleContract`, its output rules, and its total state rule described desired
  behavior;
- rule-local output schedules and the state schedule proved particular
  behavioral computations were available;
- `CompleteCombinationalOrder` checked the entire declared child graph,
  including hardware outside a particular public output cone; and
- `Module.evaluate` provided recursively constructed executable behavior.

The roles were conceptually distinct but were stored together in
`CompositeImplementation`. That dependent package was convenient but obscured
the separation.

### Rule-local schedules were intentional

Each output rule had its own `OutputRuleSchedule`. The schedule began with only
that rule's declared parent inputs and could call individual rules of child
modules. It therefore preserved precise same-cycle dependency information
through hierarchy.

The one-entry FIFO separately defined:

- `forwardSchedule` for `bValid` and `bData`;
- `readySchedule` for `aReady`;
- `stateSchedule` for coherent child transitions; and
- `combinationalOrder` for the complete structural graph.

These objects were partly repetitive, but they did not have identical jobs.
The local schedules established precise public dependencies. The complete order
ensured that an unused loop could not hide outside those local cones.

### The critical partial-output hierarchy regression

The original backend contains a bidirectional DualNot composition designed to
reject whole-instance dependency summaries. Two composite children are
connected in opposite directions. Treating either child as requiring all its
inputs creates a false apparent cycle. Calling its independent forward and
backward output rules remains acyclic.

That example demonstrated an essential property:

> A parent must be able to use one child output rule when only that rule's
> declared inputs are available.

This was not incidental FIFO machinery. It was a generic hierarchy pressure
test.

### Original strengths and weaknesses

The original architecture also provided:

- generic data-bearing contracts and modules parameterized by `SignalKind`;
- closed, recognizable primitive identities;
- naming and definition sharing separate from behavior; and
- coherent state-input scheduling for stateful children.

Its main semantic weakness was that the source hierarchy still obtained much
of its executable meaning through child contract rules and schedules. The final
old architecture review proposed a direct recursive structural solution
relation and required existence, uniqueness, evaluator agreement, and contract
refinement to be proved separately. Silean 2 is the experiment implementing
that proposal.

## What Silean 2 improves

### Independent structural meaning

`ModuleStructure` contains primitive leaves or a composite body plus one exact
child structure for every named instance. It contains no behavioral contract,
schedule, evaluator, or emitted name.

`ModuleStructure.IsSolution inputs currentState proposal` recursively requires:

- primitive output and next-state equations;
- child equations at inputs derived through wiring; and
- equality between every composite boundary output and its structural source.

This relation contains no evaluation order. It is a better semantic center than
scheduled execution.

### Existence and uniqueness are explicit

Silean 2 distinguishes:

- `HasAtMostOneSolution`, proved using child uniqueness and an availability
  schedule;
- `ModuleCycleCertified.hasStructuralResult`, which constructively proves that
  a satisfying proposal exists; and
- `ModuleCycleCertified.hasExactlyOneStructuralResult`, which combines that
  existence with uniqueness.

This cleanly supports the intended interpretation of schedules as solver
certificates rather than circuit meaning.

### Contract and structural state are independent

Primitive leaves own local structural state. Composite structural state is
derived recursively from actual child instance names and child modules.

A `ModuleCycleContract` separately owns state chosen for behavioral clarity.
`stateCorresponds` relates this contract state to structural state. For the
FIFO, abstract `storedValid` and `storedData` correspond to the two structural
EnabledRegister storage occurrences.

This is an improvement over requiring a parent state interface and a bijective
mapping that largely mirrors child state ownership.

### Refinement has the right quantification

`Implements` does not mention a schedule or evaluator. It requires every
satisfying structural proposal at corresponding current states to produce
outputs and next structural state consistent with the contract.

The resulting claim is stronger and clearer than merely showing that one
chosen evaluator returns the contract result:

> Any assignment satisfying the structural equations has the specified
> behavior.

Existence and uniqueness then establish that there is exactly one such
assignment.

### Finite symbolic foundations are cleaner

`Enumeration`, `EnumeratedMap`, `SignalMap`, derived enumeration instances, and
symbolically labelled endpoints reduce repeated `values`/`nodup`/`locate`
transcripts while retaining canonical executable identity. `SignalType` also
extends the old bit/vector vocabulary with tuples.

## Structural rules and unavailable inputs

This section records the evaluator-oriented design found during the review.
It is retained as design history; the later corrective outcomes describe the
replacement and removal of that machinery.

### What a structural rule means

A `StructuralRule` is not a behavioral contract rule. It is a semantic
dependency fact about a structure:

> Among arbitrary satisfying proposals at the same structural state, agreement
> on `reads` implies agreement on `writes`.

`ModuleStructure.composite_structuralRule` derives this fact from a partial
availability schedule. `composite_fullRule` is the coarser whole-interface
case.

### The generic independence proof already exists

`ExecutableStructuralRule` contains:

- a total executable `run` function;
- `respectsReads`, proving that written outputs depend only on declared reads;
  and
- `sound`, proving agreement with every satisfying proposal.

Schedule execution uses a total child-output store initialized with structural
defaults. Some not-yet-available wires therefore have placeholder values.
Availability prevents declared rule inputs from reading them, and
`respectsReads` proves the selected outputs are independent of every undeclared
input.

An earlier review statement that this generic guarantee was absent was wrong.
The guarantee is present and is used by the schedule replay proof.

## The actual rule-local regression

The foundation can express rule-local structural dependencies, but certified
modules do not expose them systematically.

`EnabledRegister` is the successful example. Its public current-value
structural rule is derived from a partial schedule that reads no module inputs.
The complete evaluator can then provide an executable implementation of that
partial rule because `respectsReads` proves independence from the unrelated
next-state inputs.

Other current examples are too coarse:

- `OneEntryFifo` exports one full structural rule reading all inputs and writing
  all outputs, despite its contract having separate forward and ready rules;
- hierarchical DualNot does not export separate structural forward and
  backward rules;
- RepeatedDualNot uses a combined child rule; and
- Silean 2 has no equivalent of the old bidirectional partial-output hierarchy
  regression.

Consequently, a parent using OneEntryFifo as a child cannot currently select a
published ready-only structural rule when data inputs are unavailable, even
though the semantic foundation is capable of representing one.

## A possible improvement over handwritten output schedules

It should be possible to derive a structural dependency rule generically from
each rule of a `ModuleCycleCertified` value.

For a fixed structural state:

1. `hasCorrespondingState` supplies a corresponding contract state.
2. Take two satisfying structural proposals whose inputs agree on one contract
   rule's declared reads.
3. `implements` says both proposals' outputs satisfy that contract rule at the
   same contract state.
4. The deterministic contract rule therefore gives equal values for its
   declared writes.

This should yield a generic operation conceptually like:

```text
certified structural module + named contract rule
    -> StructuralRule certified.moduleStructure
```

A complete structural evaluator can then produce the corresponding
`ExecutableStructuralRule` using the existing generic
`StructuralEvaluator.executableRule` operation.

If this theorem works, Silean 2 can improve on the old arrangement:

- a module author proves structural-to-contract refinement once;
- the exact structural dependency views follow from certified contract rules;
- a parent schedules those views individually; and
- a separate complete structural schedule still proves whole-netlist existence,
  uniqueness, and absence of hidden unused loops.

The intended interface would therefore contain both:

```text
one complete structural schedule/evaluator
one generically derived structural rule for each certified contract rule
```

The complete schedule does not replace the rule-local views.

## Genericity regression

The Silean 2 foundation supports recursive `SignalType` values:

- bit;
- vector; and
- tuple.

The useful data-bearing modules nevertheless use bits for everything:

- Mux data inputs and result are bits;
- EnabledRegister's stored value is a bit; and
- OneEntryFifo's data input, output, and stored data are bits.

The old modules and contracts parameterized their data paths by `SignalKind`.
Valid, ready, enable, and select were bits while data remained generic.

Silean 2 should recover the same distinction using `SignalType`. Aggregate data
should be implemented compositionally from the deliberately single-bit storage
and Boolean-control leaves. The richer tuple type makes the target foundation
potentially better than the original, but that potential is not exercised by
the current reusable modules.

## Primitive-boundary regression

The original architecture deliberately replaced arbitrary primitive behavior
with a closed `PrimitiveDescription` identity. Each leaf was recognizable and
had independently defined semantics and lowering.

The current Silean 2 `Primitive` is an open record containing ports, local
state, output and next-state functions, and an input-dependency proof.
`ModuleStructure.primitive` therefore accepts a leaf containing arbitrary Lean
behavior.

This creates two problems:

1. structural identity and semantic behavior are mixed again; and
2. a shallow Verilog renderer cannot know how to emit an arbitrary primitive
   value.

The documentation is inconsistent with the implementation. `Design.md` still
describes a closed single-bit primitive identity, while `Primitive.lean`
contains the open record introduced during later organization work.

Before rendering or a larger module library, the design must explicitly choose
one of:

- restore a closed primitive identity with separately defined semantics; or
- require every extensible primitive to carry or reference a separately
  registered renderable description whose semantics are proved.

An unrestricted semantic record should not silently be treated as a Verilog
primitive.

## Proof-composition and verbosity problem

The Silean 2 one-entry FIFO file is approximately the same length as the old
one despite omitting generic data, naming, lowering, and temporal machinery.
Its `Implements` proof manually unfolds and transports:

- parent-to-child input calculation;
- child proposals and satisfying equations;
- boundary output aliases;
- child contract evaluations;
- structural-to-contract current state; and
- structural-to-contract next state.

The stronger independent refinement theorem justifies some additional work,
but this amount of repeated plumbing should not be the normal proof shape.

The missing generic laws are likely to include:

- deriving structural dependency rules from certified contract rules;
- transporting a certified child rule through parent wiring;
- exposing a certified child output at a parent boundary;
- combining several certified child rule results into a parent rule; and
- assembling child next-state correspondences into the parent's recursively
  labelled structural state.

These laws must be generic. FIFO-specific helper APIs or tactics would hide the
problem rather than solve it.

## Packaging and file-organization concerns identified before correction

The former `StructuralRules.lean` owned several distinguishable concepts:

- semantic structural dependency rules;
- executable rule interfaces;
- availability predicates;
- structural schedules;
- schedule replay between arbitrary solutions; and
- composite uniqueness.

The former `StructuralEvaluation.lean` owned the mutable-looking functional store,
schedule execution, replay against child evaluators, and construction of
composite evaluators.

That organization has now been replaced by the following public order:

```text
structural equations
dependency facts
availability schedules
uniqueness
behavioral refinement
```

`ModuleCycleCertified` now packages structure, contract, state correspondence
and coverage, structural existence and uniqueness, and refinement. Local
schedules remain private proof terms beside module definitions; executable
rule views and chosen structural evaluators are no longer part of the design.

## Documentation accuracy

The chronological roadmap correctly warns that earlier outcomes may be
superseded. The current design documentation still contains claims that no
longer match the implementation, particularly the closed primitive statement.

The architecture checkpoint also concludes that remaining refinement verbosity
mostly reflects concrete wiring. The FIFO result provides contrary evidence:
much of the verbosity is repeated hierarchical transport that should be tested
for generic abstraction.

Documentation should be updated only after the corrective experiment resolves
the intended certified-module interface.

## Recommended corrective experiment

Before modifying the FIFO or adding another useful module, construct one small
generic partial-output hierarchy based on the old regression:

```text
child rule forward:
  reads forward input
  writes forward output

child rule backward:
  reads backward input
  writes backward output

two child instances:
  forward dependencies flow one direction
  backward dependencies flow the opposite direction
```

Acceptance criteria:

1. A whole-instance dependency summary exhibits the false apparent cycle.
2. Rule-local structural dependencies schedule successfully.
3. The child structural rules are derived generically from certified contract
   rules rather than from parent knowledge of child internals.
4. A complete parent schedule constructs a satisfying proposal.
5. Child uniqueness plus the complete parent schedule proves at-most-one.
6. The parent therefore has exactly one structural solution.
7. Each executable rule is proved independent of unrelated child inputs.
8. No handwritten primitive occurrence paths or positional port transcripts
   are introduced.
9. The focused build remains below five seconds.

If generic certified-rule derivation succeeds, adopt it as the normal child
interface and simplify existing modules around it. If it fails, restore
explicit per-output structural schedules to the reusable module interface
before continuing.

## Recommended recovery sequence

1. Implement and test generic structural-rule derivation from
   `ModuleCycleCertified` using the bidirectional partial-output example.
2. Decide the reusable certified-module package after observing which evaluator
   and uniqueness evidence that derivation actually requires.
3. Correct the primitive boundary and reconcile the design documents.
4. Generalize Mux and EnabledRegister data over `SignalType`.
5. Generalize OneEntryFifo data using those reusable modules.
6. Extract only the generic hierarchical refinement laws demonstrated by the
   generalized FIFO proof.
7. Re-review file ownership, terminology, and focused build times.
8. Resume shallow Verilog-facing work only after arbitrary semantic primitive
   records can no longer reach rendering unnoticed.

## Final assessment

Silean 2 is not a failed rewrite. Its order-independent structural solution,
explicit uniqueness, abstract contract state, and refinement over arbitrary
solutions are meaningful improvements and directly answer the most important
open issue in the old architecture.

It is also not yet a reliable replacement foundation. The old project's
partial-output hierarchy guarantee is not represented in the current reusable
module API or regression suite, generic datapaths were lost in the concrete
library, the primitive boundary became less suitable for rendering, and the
FIFO proof exposed missing generic composition support.

The next step should be a small falsifiable architectural experiment, not more
FIFO-specific proof work and not a broad rewrite. Its purpose is to show that
certification can generically recover precise rule-local child evaluation while
retaining the new independent structural semantics.

## Corrective review outcome (2026-08-26)

The bidirectional two-rule regression now passes with the stronger separation
the review requested:

- `ModuleCycleCertified.structuralRule` derives the semantic dependency fact
  for any named contract rule solely from state coverage and `Implements`.
- A parent `Certified.Schedule` contains only named occurrences of rules from a
  family of certified children. It contains no child schedule, structural
  implementation rule, executable rule, or evaluator.
- The forward parent rule calls `a.forward` then `b.forward`; the backward rule
  calls `b.backward` then `a.backward`; state has its one separate schedule.
- Generic combination replays those schedules, omits duplicate occurrences,
  and the parent proves that every immediate child contract rule is covered.
- The combined schedule generically proves at-most-one structural solution.
  Child-certified existence and refinement are sufficient to construct a
  satisfying proposal for the concrete parent, and the parent is certified to
  implement its two-rule identity contract.
- A negative theorem shows that neither whole child can start when both of its
  inputs are summarized together. The rule-local interface therefore fixes the
  old false-cycle regression rather than merely making the positive example
  compile.

The architectural decision is to adopt named certified contract rules as the
normal hierarchical scheduling interface. Schedules are local proof terms and
do not belong in `ModuleCycleCertified`. The certificate now carries
propositional structural existence and uniqueness, so it guarantees exactly
one structural result without publishing a chosen evaluator.

`StructuralRule` remains useful as the semantic theorem derived from a child
certificate and now lives in the independent `StructuralDependency` layer.
`ExecutableStructuralRule` and `StructuralEvaluator` are not used by the new
hierarchical path. BitMux and its useful dependent chain—EnabledRegister,
FifoControl, and OneEntryFifo—have now been migrated. Their public definitions
contain certified children, rule-local schedules used only to prove uniqueness,
constructive structural existence, and contract refinement; they expose no
chosen evaluator or executable structural rule.

This migration also exposed a dependent-elaboration problem: opaque port and
certified-child projections made equal bit types difficult for Lean to identify.
The relevant module port maps and the generic certified child-structure
projection are now reducible. This is representation transparency, not a new
module-specific proof device.

Focused evidence: the complete `OneEntryFifo` dependency target builds in about
2 seconds when its prerequisites are warm. The migrated files contain no
`sorry`, `admit`, `Classical.choice`, or `native_decide`.

## Legacy evaluator removal outcome

The follow-up audit found only one non-legacy dependency: the original
HierarchicalDualNot certificate imported its uniqueness theorem from
`StructuralRuleChecks`. It now defines certified NOT children and proves
uniqueness with two named child-rule schedules, one for each independent
contract rule. Its structural existence proof likewise uses the certified
children rather than a selected evaluator.

After that migration, `StructuralRules.lean`, `StructuralEvaluation.lean`,
`StructuralRuleChecks.lean`, and `StructuralEvaluationChecks.lean` had no
foundational consumers and were removed. `StructuralDependency.lean` remains
because `StructuralRule` and `HasAtMostOneSolution` are semantic propositions.
`CertifiedSchedule.lean` remains because its schedules are positive
availability/acyclicity evidence used to prove uniqueness. Contract evaluation
in `ModuleCycleEvaluation.lean` is unrelated and remains: it applies declared
behavioral rules, not structural schedules.

The resulting separation is now literal in the import graph: structural
equations do not import schedules; semantic dependency facts do not import a
program; certified schedules import the certificate interface; and useful
modules construct existence and prove refinement without publishing an
evaluation choice.
