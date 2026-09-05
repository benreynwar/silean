import Silean.Contracts.Cycle.CycleContract
import Silean.Structure.ModuleStructure
import Silean.Primitives.NotPrimitive

namespace Silean.Examples.Fixtures.DoubleNot

open Silean

inductive Instance
  | first
  | second
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .first | .second => Primitives.not.ports

inductive Input
  | value
deriving Enumeration

inductive Output
  | result
deriving Enumeration

def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .value => .bit

def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .result => .bit

def ports : ModulePorts := ⟨inputMap, outputMap⟩

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .result => context.instanceOutput .second .output
  instanceInput
    | .first, .input => context.moduleInput .value
    | .second, .input => context.instanceOutput .first .output

def body : ModuleBody where
  context := context
  wiring := wiring

end Silean.Examples.Fixtures.DoubleNot

namespace Silean.Examples.Fixtures.DoubleNot
open Silean
def childStructure : (name : Examples.Fixtures.DoubleNot.instancePorts.Name) →
    ModuleStructure (Examples.Fixtures.DoubleNot.instancePorts.ports name)
  | .first | .second => .primitive Primitives.not
def moduleStructure : ModuleStructure Examples.Fixtures.DoubleNot.ports :=
  .composite Examples.Fixtures.DoubleNot.body childStructure
end Silean.Examples.Fixtures.DoubleNot

namespace Silean.Examples.Fixtures.DoubleNot
open Silean
inductive Rule | apply
deriving Enumeration
def outputRule : Contracts.Cycle.CycleOutputRule Examples.Fixtures.DoubleNot.ports emptySignalMap :=
  { readsInputs := .all Examples.Fixtures.DoubleNot.ports.inputs
    writesOutputs := .all Examples.Fixtures.DoubleNot.ports.outputs
    target := fun inputs _ => fun | .result => inputs .value }
def cycleContract : Contracts.Cycle.ModuleCycleContract Examples.Fixtures.DoubleNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty Examples.Fixtures.DoubleNot.ports
  outputCoverage := by rfl
end Silean.Examples.Fixtures.DoubleNot
