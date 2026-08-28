import Silean.ModuleCycleContract
import Silean.Examples.Fixtures.HierarchicalDualNot

namespace Silean.Examples.Fixtures.RepeatedDualNot

open Silean

inductive Instance
  | first
  | second
deriving Enumeration

@[reducible] def instances : Instances :=
  EnumeratedMap.of Instance fun
    | .first | .second => Examples.Fixtures.HierarchicalDualNot.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instances := instances

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instances where
  moduleOutput
    | .forward => context.instanceOutput .second .forward
    | .backward => context.instanceOutput .second .backward
  instanceInput
    | .first, .forward => context.moduleInput .forward
    | .first, .backward => context.moduleInput .backward
    | .second, .forward => context.instanceOutput .first .forward
    | .second, .backward => context.instanceOutput .first .backward

def body : ModuleBody := ⟨context, wiring⟩

def childStructure : (name : instances.Name) → ModuleStructure (instances.ports name)
  | .first | .second => Examples.Fixtures.HierarchicalDualNot.moduleStructure

def moduleStructure : ModuleStructure ports :=
  .composite body childStructure

end Silean.Examples.Fixtures.RepeatedDualNot

namespace Silean.Examples.Fixtures.RepeatedDualNot
open Silean
def inputSelection : (input : Examples.Fixtures.DualNot.Input) →
    SignalSelection Examples.Fixtures.DualNot.ports.inputs (.ofList [.bit])
  | .forward => Examples.Fixtures.DualNot.ports.inputs.select .forward
  | .backward => Examples.Fixtures.DualNot.ports.inputs.select .backward
def outputSelection : (output : Examples.Fixtures.DualNot.Output) →
    SignalSelection Examples.Fixtures.DualNot.ports.outputs (.ofList [.bit])
  | .forward => Examples.Fixtures.DualNot.ports.outputs.select .forward
  | .backward => Examples.Fixtures.DualNot.ports.outputs.select .backward
def outputRule (input : Examples.Fixtures.DualNot.Input) (output : Examples.Fixtures.DualNot.Output) :
    CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap (.ofLists [.bit] [.bit]) where
  readsInputs := inputSelection input
  writesOutputs := outputSelection output
  target | (value, ()), _ => (value, ())
inductive Rule | forward | backward
deriving Enumeration
def cycleContract : ModuleCycleContract Examples.Fixtures.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, outputRule .forward .forward⟩
    | .backward => ⟨_, outputRule .backward .backward⟩
  stateRule := CycleStateRule.empty Examples.Fixtures.DualNot.ports
  outputCoverage := by rfl
end Silean.Examples.Fixtures.RepeatedDualNot
