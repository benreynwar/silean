# Leafwise aggregate composition

This document records the reviewed abstraction for modules that apply the same
operation independently to every immediate component of a `SignalType`. It is
the design rationale for `LeafwiseComposition.lean`, not a compatibility or
historical record.

## The common hierarchy

For a vector or tuple, Register, Mask, and BitwiseOr all have the same physical
shape:

1. one splitter instance for each recursively shaped public input;
2. one recursively certified component instance for each immediate signal
   component;
3. one combiner instance for each recursively shaped public output; and
4. direct broadcast wiring for fixed-shape public inputs.

The module boundary labels remain chosen by the module. `Composition.LeafwiseInterface`
classifies those labels as recursive or fixed only for constructing the
hierarchy. It does not expose artificial unary/pair APIs.

| Module | Recursive inputs | Fixed inputs | Recursive outputs | Contract state |
| --- | --- | --- | --- | --- |
| Register | `input : T` | none | `output : T` | `stored : T` |
| Mask | `value : T` | `mask : bit` | `result : T` | none |
| BitwiseOr | `left : T`, `right : T` | none | `result : T` | none |

This is the important difference between the three cases. A fixed input is not
split and does not create an adapter instance; the same source is wired to the
corresponding input of every component.

## What is generic

`LeafwiseComposition.lean` owns the shared structural construction:

- typed aggregate instance names (`splitter`, `component`, `combiner`);
- their enumeration, ports, context, and total wiring;
- the recursive `ModuleStructure` construction;
- the corresponding certified-child family and generic child-rule
  occurrences; and
- finite component-family scheduling after an existing availability prefix.

Structural existence has one generic proof. `AggregateProposalConstruction` asks a
module for four readable views of its wiring: splitter inputs, component
inputs, combiner inputs, and boundary outputs. Four equations connect those
views to the actual wiring. `AggregateProposalConstruction.hasStructuralResult` then
enumerates the splitter, recursive component, and combiner certificates and
constructs a satisfying composite proposal. The construction is a private proof
witness; it is not retained in `Contracts.Cycle.ModuleCycleCertified` or in the structure.

This boundary removes the formerly repeated dependent enumeration and proposal
assembly while keeping each module's wiring equations visible.

## Scheduling and uniqueness

The scheduling pattern is shared, but the required calls are determined by the
module contract:

- Register's output rule reads contract state, so its output schedule calls the
  component output rules and the combiner. Its state schedule calls the input
  splitter so that every child register receives its next-state input.
- Mask's output rule calls its value splitter, every component Mask rule, and
  the combiner. Its mask bit is already a boundary input and is broadcast.
- BitwiseOr's output rule calls both operand splitters, every component
  BitwiseOr rule, and the combiner.
- Mask and BitwiseOr have empty child state reads, so their state schedules are
  empty.

The generic schedule library owns finite-family construction and selected
dependency scheduling. `Composition.LeafwiseInterface.callComponentsAfter` specializes
that genuinely shared operation to the component family. The module files keep
the readiness proofs that explain why their particular contract reads are
available. Moving those proofs into a record would not make them generic; it
would only hide the dependency argument.

Once output and state schedules are supplied, the existing generic
`RuleSchedules.hasAtMostOneSolution` theorem proves structural uniqueness.
Coverage remains a small module proof because it states which parent contract
rule exercises each child contract rule.

## State correspondence and refinement

State correspondence is intentionally semantic rather than structural.
Register maps its aggregate contract state to the contract states of recursive
component registers and delegates correspondence to their certificates. Mask
and BitwiseOr have no contract state, so correspondence is trivial.

Refinement is also operation-specific. The shared proof shape is:

1. destruct a satisfying composite proposal into boundary and child facts;
2. apply each component's public `implements` proof;
3. use splitter/combiner laws to reassemble component results; and
4. prove the parent contract rule and next-state correspondence.

The actual algebra differs: identity/storage for Register, broadcast masking
for Mask, and pointwise disjunction for BitwiseOr. A purported generic theorem
would need these exact semantic proofs as parameters and would therefore only
relocate the module proof. They remain in the module files.

## Retention decision

Retain the structural and existence abstraction. It represents a real class of
hierarchies, supports any finite number of recursive and fixed public inputs,
and has been validated by all three materially different modules. It also
centralizes the difficult dependent proposal construction.

Do not add a monolithic “leafwise certification” wrapper. Schedules should
continue to expose contract dependencies, and state/refinement proofs should
continue to expose module semantics. Add another generic law only when at least
two modules can consume it with less proof and clearer types.

## Measured result

Relative to the repository state before this change, the reusable module files
became smaller:

| File | Before | After | Change |
| --- | ---: | ---: | ---: |
| `Register.lean` | 771 | 705 | -66 |
| `Mask.lean` | 851 | 785 | -66 |
| `BitwiseOr.lean` | 969 | 881 | -88 |

The new generic foundation is 549 lines, so this is not a total-line-count win
for only three consumers. Its value is instead that the dependent hierarchy,
wiring, child enumeration, and proposal-existence proof now have one checked
definition, while 220 lines disappeared from the operation modules. A fourth
leafwise operation can provide an interface, four construction equations, its
dependency schedules, and its semantic refinement without copying that
foundation.

The former aggregate existence proofs each manually selected splitter
proposals, enumerated heterogeneous component proposals, selected combiner
proposals, assembled the dependent child function, and reproved the same four
wiring cases. They now contain only an
`AggregateProposalConstruction` value and one application of the generic
existence theorem. Component-family scheduling similarly uses one generic
constructor, while the meaningful readiness proofs remain beside each module.

A clean full build reported focused compilation times of 1.3 seconds for the
generic foundation, 2.4 seconds for Register, 3.1 seconds for Mask, and 3.1
seconds for BitwiseOr. Independent five-second-bounded checks also passed for
all three modules. These results satisfy the five-second focused-target limit.
