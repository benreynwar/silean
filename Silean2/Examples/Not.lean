import Silean2.ModuleCycleContract
import Silean2.ModuleStructure
import Silean2.Primitives.Not

namespace Silean2.Examples.Not

open Silean2

inductive Instance
  | inverter
deriving Enumeration

@[reducible] def instances : Instances :=
  EnumeratedMap.of Instance fun
    | .inverter => Primitives.not.ports

inductive Input
  | value
deriving Enumeration

inductive Output
  | inverted
deriving Enumeration

def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .value => .bit

def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .inverted => .bit

def ports : ModulePorts := ⟨inputMap, outputMap⟩

@[reducible] def context : EndpointContext where
  ports := ports
  instances := instances

def wiring : Wiring context.ports context.instances where
  moduleOutput
    | .inverted => context.instanceOutput .inverter .output
  instanceInput
    | .inverter, .input => context.moduleInput .value

def body : ModuleBody where
  context := context
  wiring := wiring

end Silean2.Examples.Not

namespace Silean2.Examples.Not

open Silean2

def childStructure : (name : Examples.Not.instances.Name) →
    ModuleStructure (Examples.Not.instances.ports name)
  | .inverter => .primitive Primitives.not

def moduleStructure : ModuleStructure Examples.Not.ports :=
  .composite Examples.Not.body childStructure

end Silean2.Examples.Not

namespace Silean2.Examples.Not

open Silean2

inductive Rule | apply
deriving Enumeration

def outputRule : CycleOutputRule Examples.Not.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.Not.inputMap.select .value
  writesOutputs := Examples.Not.outputMap.select .inverted
  target | (value, ()), _ => (!value, ())

def cycleContract : ModuleCycleContract Examples.Not.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule⟩
  stateRule := CycleStateRule.empty Examples.Not.ports
  outputCoverage := by rfl

end Silean2.Examples.Not
