import Silean.ModuleCycleContract
import Silean.Structure.ModuleStructure
import Silean.Primitives.Not

namespace Silean.Examples.Fixtures.Not

open Silean

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

end Silean.Examples.Fixtures.Not

namespace Silean.Examples.Fixtures.Not

open Silean

def childStructure : (name : Examples.Fixtures.Not.instances.Name) →
    ModuleStructure (Examples.Fixtures.Not.instances.ports name)
  | .inverter => .primitive Primitives.not

def moduleStructure : ModuleStructure Examples.Fixtures.Not.ports :=
  .composite Examples.Fixtures.Not.body childStructure

end Silean.Examples.Fixtures.Not

namespace Silean.Examples.Fixtures.Not

open Silean

inductive Rule | apply
deriving Enumeration

def outputRule : CycleOutputRule Examples.Fixtures.Not.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.Fixtures.Not.inputMap.select .value
  writesOutputs := Examples.Fixtures.Not.outputMap.select .inverted
  target | (value, ()), _ => (!value, ())

def cycleContract : ModuleCycleContract Examples.Fixtures.Not.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule⟩
  stateRule := CycleStateRule.empty Examples.Fixtures.Not.ports
  outputCoverage := by rfl

end Silean.Examples.Fixtures.Not
