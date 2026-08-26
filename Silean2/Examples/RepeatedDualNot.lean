import Silean2.ModuleCycleContract
import Silean2.Examples.HierarchicalDualNot

namespace Silean2.Examples.RepeatedDualNot

open Silean2

inductive Instance
  | first
  | second
deriving Enumeration

@[reducible] def instances : Instances :=
  EnumeratedMap.of Instance fun
    | .first | .second => Examples.HierarchicalDualNot.ports

@[reducible] def context : EndpointContext where
  ports := Examples.DualNot.ports
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
  | .first | .second => Examples.HierarchicalDualNot.moduleStructure

def moduleStructure : ModuleStructure ports :=
  .composite body childStructure

end Silean2.Examples.RepeatedDualNot

namespace Silean2.Examples.RepeatedDualNot
open Silean2
def inputSelection : (input : Examples.DualNot.Input) →
    SignalSelection Examples.DualNot.ports.inputs (.ofList [.bit])
  | .forward => Examples.DualNot.ports.inputs.select .forward
  | .backward => Examples.DualNot.ports.inputs.select .backward
def outputSelection : (output : Examples.DualNot.Output) →
    SignalSelection Examples.DualNot.ports.outputs (.ofList [.bit])
  | .forward => Examples.DualNot.ports.outputs.select .forward
  | .backward => Examples.DualNot.ports.outputs.select .backward
def outputRule (input : Examples.DualNot.Input) (output : Examples.DualNot.Output) :
    CycleOutputRule Examples.DualNot.ports emptySignalMap (.ofLists [.bit] [.bit]) where
  readsInputs := inputSelection input
  writesOutputs := outputSelection output
  target | (value, ()), _ => (value, ())
inductive Rule | forward | backward
deriving Enumeration
def cycleContract : ModuleCycleContract Examples.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, outputRule .forward .forward⟩
    | .backward => ⟨_, outputRule .backward .backward⟩
  stateRule := CycleStateRule.empty Examples.DualNot.ports
  outputCoverage := by rfl
end Silean2.Examples.RepeatedDualNot
