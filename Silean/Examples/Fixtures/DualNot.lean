import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.Fixtures.DualNot

open Silean

inductive Input
  | forward
  | backward
deriving Enumeration

inductive Output
  | forward
  | backward
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .forward | .backward => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .forward | .backward => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

end Silean.Examples.Fixtures.DualNot

namespace Silean.Examples.Fixtures.DualNot
open Silean
inductive Rule | forward | backward
deriving Enumeration

inductive RuleSignal | value deriving Enumeration

@[reducible] def ruleInput (input : Input) : SignalGroup ports.inputs :=
  SignalGroup.fromLabels ports.inputs RuleSignal fun | .value => input

@[reducible] def ruleOutput (output : Output) : SignalGroup ports.outputs :=
  SignalGroup.fromLabels ports.outputs RuleSignal fun | .value => output

def forwardRule : Contracts.Cycle.CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap :=
  { readsInputs := ruleInput .forward
    writesOutputs := ruleOutput .forward
    target := fun inputs _ => fun | .value => !(inputs .value) }
def backwardRule : Contracts.Cycle.CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap :=
  { readsInputs := ruleInput .backward
    writesOutputs := ruleOutput .backward
    target := fun inputs _ => fun | .value => !(inputs .value) }
def stateRule : Contracts.Cycle.CycleStateRule Examples.Fixtures.DualNot.ports emptySignalMap :=
  Contracts.Cycle.CycleStateRule.empty Examples.Fixtures.DualNot.ports
def cycleContract : Contracts.Cycle.ModuleCycleContract Examples.Fixtures.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => forwardRule
    | .backward => backwardRule
  stateRule := stateRule
  outputCoverage := by rfl

@[simp] theorem forwardRule_holds_iff (inputs : ports.inputs.Values)
    (state : emptySignalMap.Values) (outputs : ports.outputs.Values) :
    forwardRule.Holds inputs state outputs ↔ outputs .forward = !inputs .forward := by
  unfold forwardRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext output
    cases output
    exact equal

@[simp] theorem backwardRule_holds_iff (inputs : ports.inputs.Values)
    (state : emptySignalMap.Values) (outputs : ports.outputs.Values) :
    backwardRule.Holds inputs state outputs ↔ outputs .backward = !inputs .backward := by
  unfold backwardRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext output
    cases output
    exact equal
end Silean.Examples.Fixtures.DualNot
