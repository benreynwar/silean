import Silean2.DeriveEnumeration

namespace Silean2

/-! An ordered selection of labels from one signal map. The result index records
the selected signal types, so projected values remain heterogeneous and typed. -/

inductive SignalSelection (signals : SignalMap) : SignalTypes → Type
  | nil : SignalSelection signals .nil
  | cons (label : signals.Label) (tail : SignalSelection signals types) :
      SignalSelection signals (.cons (signals.signalType label) types)

namespace SignalSelection

def prepend (tail : SignalSelection signals types) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) types) :=
  .cons label tail

def labels : SignalSelection signals types → List signals.Label
  | .nil => []
  | .cons label tail => label :: tail.labels

def project (selection : SignalSelection signals types)
    (values : signals.Values) : types.Denote :=
  match selection with
  | .nil => ()
  | .cons label tail => (values label, tail.project values)

end SignalSelection

def SignalMap.select (signals : SignalMap) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) .nil) :=
  .cons label .nil

/-! Output rules are the observable, dependency-aware pieces of a contract.
They read a selected set of module inputs, see complete current state, and
produce a selected set of module outputs. They contain no structure or order. -/

structure CycleOutputRuleShape where
  inputTypes : SignalTypes
  outputTypes : SignalTypes

def CycleOutputRuleShape.ofLists (inputTypes outputTypes : List SignalType) :
    CycleOutputRuleShape where
  inputTypes := .ofList inputTypes
  outputTypes := .ofList outputTypes

structure CycleOutputRule (ports : ModulePorts) (state : SignalMap)
    (shape : CycleOutputRuleShape) where
  readsInputs : SignalSelection ports.inputs shape.inputTypes
  writesOutputs : SignalSelection ports.outputs shape.outputTypes
  target : shape.inputTypes.Denote → state.Values →
    shape.outputTypes.Denote

abbrev SomeCycleOutputRule (ports : ModulePorts) (state : SignalMap) :=
  Sigma (CycleOutputRule ports state)

/-! Every contract has one total clock-edge transition. When its independent
`state` map is empty, the result type has one possible value and this rule
is trivial without requiring a separate combinational contract type. -/

structure CycleStateRule (ports : ModulePorts) (state : SignalMap) where
  target : ports.inputs.Values → state.Values → state.Values

def CycleStateRule.empty (ports : ModulePorts) :
    CycleStateRule ports emptySignalMap where
  target := fun _ _ => SignalMap.emptyValues

/-! A contract owns a finite readable rule identity, its output rules, exact
output coverage, and the one total state rule. The permutation says that the
concatenated write selections contain every output exactly once: the boundary
output enumeration is already duplicate-free. -/

structure ModuleCycleContract (ports : ModulePorts) where
  state : SignalMap
  RuleName : Type
  ruleNames : Enumeration RuleName
  outputRule : RuleName → SomeCycleOutputRule ports state
  stateRule : CycleStateRule ports state
  outputCoverage :
    (ruleNames.values.flatMap fun name =>
      (outputRule name).2.writesOutputs.labels).Perm ports.outputs.labels.values

namespace ModuleCycleContract

def writtenOutputs (contract : ModuleCycleContract ports) : List ports.outputs.Label :=
  contract.ruleNames.values.flatMap fun name =>
    (contract.outputRule name).2.writesOutputs.labels

theorem writtenOutputs_perm (contract : ModuleCycleContract ports) :
    contract.writtenOutputs.Perm ports.outputs.labels.values :=
  contract.outputCoverage

theorem writtenOutputs_nodup (contract : ModuleCycleContract ports) :
    contract.writtenOutputs.Nodup :=
  contract.outputCoverage.nodup_iff.mpr ports.outputs.labels.nodup

theorem output_is_written (contract : ModuleCycleContract ports)
    (output : ports.outputs.Label) : output ∈ contract.writtenOutputs := by
  exact contract.outputCoverage.mem_iff.mpr
    (ListIndex.get_eq (ports.outputs.labels.locate output) ▸
      List.get_mem _ _)

end ModuleCycleContract

end Silean2
