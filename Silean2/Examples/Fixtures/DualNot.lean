import Silean2.ModuleCycleContract

namespace Silean2.Examples.Fixtures.DualNot

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

end Silean2.Examples.Fixtures.DualNot

namespace Silean2.Examples.Fixtures.DualNot
open Silean2
inductive Rule | forward | backward
deriving Enumeration
def forwardRule : CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.Fixtures.DualNot.ports.inputs.select .forward
  writesOutputs := Examples.Fixtures.DualNot.ports.outputs.select .forward
  target | (input, ()), _ => (!input, ())
def backwardRule : CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.Fixtures.DualNot.ports.inputs.select .backward
  writesOutputs := Examples.Fixtures.DualNot.ports.outputs.select .backward
  target | (input, ()), _ => (!input, ())
def stateRule : CycleStateRule Examples.Fixtures.DualNot.ports emptySignalMap :=
  CycleStateRule.empty Examples.Fixtures.DualNot.ports
def cycleContract : ModuleCycleContract Examples.Fixtures.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, forwardRule⟩
    | .backward => ⟨_, backwardRule⟩
  stateRule := stateRule
  outputCoverage := by rfl
end Silean2.Examples.Fixtures.DualNot
