import Silean.ModuleCycleContract
import Silean.Structure.ModuleStructure
import Silean.Primitives.Not

namespace Silean.Examples.Fixtures.DoubleNot

open Silean

inductive Instance
  | first
  | second
deriving Enumeration

@[reducible] def instances : Instances :=
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
  instances := instances

def wiring : Wiring context.ports context.instances where
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
def childStructure : (name : Examples.Fixtures.DoubleNot.instances.Name) →
    ModuleStructure (Examples.Fixtures.DoubleNot.instances.ports name)
  | .first | .second => .primitive Primitives.not
def moduleStructure : ModuleStructure Examples.Fixtures.DoubleNot.ports :=
  .composite Examples.Fixtures.DoubleNot.body childStructure
end Silean.Examples.Fixtures.DoubleNot

namespace Silean.Examples.Fixtures.DoubleNot
open Silean
inductive Rule | apply
deriving Enumeration
def outputRule : CycleOutputRule Examples.Fixtures.DoubleNot.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := Examples.Fixtures.DoubleNot.ports.inputs.select .value
  writesOutputs := Examples.Fixtures.DoubleNot.ports.outputs.select .result
  target | (input, ()), _ => (input, ())
def cycleContract : ModuleCycleContract Examples.Fixtures.DoubleNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule⟩
  stateRule := CycleStateRule.empty Examples.Fixtures.DoubleNot.ports
  outputCoverage := by rfl
end Silean.Examples.Fixtures.DoubleNot
