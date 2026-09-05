# Cycle-rule foundation

## Purpose

Cycle rules describe behavioral dependencies and equations. Their source
should therefore show signal names and behavior, not repeat port types or
encode values as nested positional tuples.

The previous rule representation exposed three implementation details:

- a `CycleOutputRuleShape` containing types already known by the ports;
- `SignalSelection` values assembled with `prepend`; and
- `SignalTypes.Denote` tuples accessed through `.1`, `.2.1`, and deeper paths.

The PicoRV ALU formerly repeated seventeen input types and immediately unpacked
a seventeen-deep tuple back into named fields. That noise was unrelated to its
behavior.

## Audited requirements

The evaluation, scheduling, structural-existence, and certification code needs
only the following facts and operations:

1. Each rule has an ordered list of parent input labels that it reads.
2. Each output rule has an ordered list of parent output labels that it writes.
3. Complete input values can be projected to the rule's inputs.
4. Rule results can be compared with, and written into, complete output values.
5. Equality on the read labels implies equality of projected inputs.
6. Two matching results agree at every written parent label.

Schedules inspect only the embedded `readsInputs.labels` and
`writesOutputs.labels`. They do not need a positional tuple type.

## Implemented representation

`SignalGroup parent` is a finite named `SignalMap` embedded type-correctly into
a parent map:

```lean
structure SignalGroup (parent : SignalMap) where
  signals : SignalMap
  embed : signals.Label → parent.Label
  preservesType : ∀ label,
    signals.signalType label = parent.signalType (embed label)
```

It provides ordered embedded `labels`, `project`, `Matches`, and `write`.
`SignalGroup.all` and `SignalGroup.empty` cover the common complete and empty
cases. `SignalGroup.fromLabels` creates a genuinely partial named group while
inheriting every signal type from its parent, so a rule never repeats those
types or supplies type-preservation proofs.

Output rules now store groups directly:

```lean
structure CycleOutputRule (ports : ModulePorts) (state : SignalMap) where
  readsInputs : SignalGroup ports.inputs
  writesOutputs : SignalGroup ports.outputs
  target : readsInputs.signals.Values → state.Values →
    writesOutputs.signals.Values
```

`CycleStateRule.readsInputs` is also a `SignalGroup`; its result was already a
complete named state valuation. `CycleOutputRuleShape`,
`PositionalCycleOutputRuleShape`, `SomeCycleOutputRule`, and the existential
rule wrapper have been removed.

Evaluation projects group values, applies `target`, and matches or writes the
named result. Structural dependency and uniqueness use the generic
`SignalGroup.project_eq_of_eq_on` and `SignalGroup.Matches.eq_of_mem` laws.

## Representative rules

The PicoRV ALU reads and writes its complete boundary, so its handwritten rule
is now:

```lean
def resultValues (result : Result) : outputMap.Values
  | .alu_out => result.alu_out
  | .alu_out_0 => result.alu_out_0

def outputRule : CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := resultValues (evaluate (valuesOf inputs))
```

There is no explicit type chain, `prepend`, or positional tuple access. The
HalfAdder and EnabledRegister source remains concise through
`module_cycle_contract`; their generated contracts have the same new public
`CycleOutputRule` and `CycleStateRule` types. RegisterBank and the PicoRV
Memory, Datapath, Regs, Decoder, and Control contracts exercise partial named
groups and complete groups without positional rule bodies.

The schedule derivation tactic recognizes complete groups directly. When a
child contract has one output rule, it uses the generic fact that this rule
writes every child output rather than repeatedly scanning the child's write
list. This preserves the existing schedule proof while avoiding quadratic work
on wide boundaries such as the decoder.

## Selection boundary

`SignalSelection` remains useful for ordered signal layouts, valid/ready
payload interfaces, and adapters that genuinely consume tuple-shaped data. It
is no longer the semantic foundation of cycle rules.

The positional cycle-rule constructors and their duplicate evaluation theory
have been removed. `module_cycle_contract` now generates private named group
labels and direct `SignalGroup` targets; generated rule bodies never pass
through tuple-shaped selections.

The decoder instruction-summary trap rule preserves its exact 39-of-40 input
dependency with a private named input group. Although that list is necessarily
large, the rule target and proof use named fields throughout and the schedule
still records the precise dependency needed by its parent.
