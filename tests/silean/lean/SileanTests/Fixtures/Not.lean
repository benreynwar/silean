import Silean.Contracts.Cycle.CycleContract
import Silean.Structure.ModuleStructure
import Silean.Primitives.NotPrimitive

namespace SileanTests.Fixtures.Not

open Silean

inductive Instance
  | inverter
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
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
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .inverted => context.instanceOutput .inverter .output
  instanceInput
    | .inverter, .input => context.moduleInput .value

def body : ModuleBody where
  context := context
  wiring := wiring

end SileanTests.Fixtures.Not

namespace SileanTests.Fixtures.Not

open Silean

def childStructure : (name : SileanTests.Fixtures.Not.instancePorts.Name) →
    ModuleStructure (SileanTests.Fixtures.Not.instancePorts.ports name)
  | .inverter => .primitive Primitives.not

def moduleStructure : ModuleStructure SileanTests.Fixtures.Not.ports :=
  .composite SileanTests.Fixtures.Not.body childStructure

end SileanTests.Fixtures.Not

namespace SileanTests.Fixtures.Not

open Silean

inductive Rule | apply
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule SileanTests.Fixtures.Not.ports emptySignalMap :=
  { readsInputs := .all SileanTests.Fixtures.Not.inputMap
    writesOutputs := .all SileanTests.Fixtures.Not.outputMap
    target := fun inputs _ => fun | .inverted => !(inputs .value) }

def cycleContract : Contracts.Cycle.ModuleCycleContract SileanTests.Fixtures.Not.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty SileanTests.Fixtures.Not.ports
  outputCoverage := by rfl

end SileanTests.Fixtures.Not
