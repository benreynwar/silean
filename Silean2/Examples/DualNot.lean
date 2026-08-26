import Silean2.ModuleCycleContract

namespace Silean2.Examples.DualNot

open Silean2

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

end Silean2.Examples.DualNot

namespace Silean2.Examples.DualNot
open Silean2
inductive Rule | forward | backward
deriving Enumeration
def forwardRule : CycleOutputRule Examples.DualNot.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.DualNot.ports.inputs.select .forward
  writesOutputs := Examples.DualNot.ports.outputs.select .forward
  target | (input, ()), _ => (!input, ())
def backwardRule : CycleOutputRule Examples.DualNot.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.DualNot.ports.inputs.select .backward
  writesOutputs := Examples.DualNot.ports.outputs.select .backward
  target | (input, ()), _ => (!input, ())
def stateRule : CycleStateRule Examples.DualNot.ports emptySignalMap :=
  CycleStateRule.empty Examples.DualNot.ports
def cycleContract : ModuleCycleContract Examples.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, forwardRule⟩
    | .backward => ⟨_, backwardRule⟩
  stateRule := stateRule
  outputCoverage := by rfl
end Silean2.Examples.DualNot
