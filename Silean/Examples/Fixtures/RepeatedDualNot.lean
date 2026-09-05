import Silean.Contracts.Cycle.CycleContract
import Silean.Examples.Fixtures.HierarchicalDualNot

namespace Silean.Examples.Fixtures.RepeatedDualNot

open Silean

inductive Instance
  | first
  | second
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .first | .second => Examples.Fixtures.HierarchicalDualNot.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instancePorts := instancePorts

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .forward => context.instanceOutput .second .forward
    | .backward => context.instanceOutput .second .backward
  instanceInput
    | .first, .forward => context.moduleInput .forward
    | .first, .backward => context.moduleInput .backward
    | .second, .forward => context.instanceOutput .first .forward
    | .second, .backward => context.instanceOutput .first .backward

def body : ModuleBody := ⟨context, wiring⟩

def childStructure : (name : instancePorts.Name) → ModuleStructure (instancePorts.ports name)
  | .first | .second => Examples.Fixtures.HierarchicalDualNot.moduleStructure

def moduleStructure : ModuleStructure ports :=
  .composite body childStructure

end Silean.Examples.Fixtures.RepeatedDualNot

namespace Silean.Examples.Fixtures.RepeatedDualNot
open Silean
inductive Rule | forward | backward
deriving Enumeration
def outputRule : Rule →
    Contracts.Cycle.CycleOutputRule Examples.Fixtures.DualNot.ports emptySignalMap
  | .forward =>
      { readsInputs := Examples.Fixtures.DualNot.ruleInput .forward
        writesOutputs := Examples.Fixtures.DualNot.ruleOutput .forward
        target := fun inputs _ => fun | .value => inputs .value }
  | .backward =>
      { readsInputs := Examples.Fixtures.DualNot.ruleInput .backward
        writesOutputs := Examples.Fixtures.DualNot.ruleOutput .backward
        target := fun inputs _ => fun | .value => inputs .value }
def cycleContract : Contracts.Cycle.ModuleCycleContract Examples.Fixtures.DualNot.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => outputRule .forward
    | .backward => outputRule .backward
  stateRule := Contracts.Cycle.CycleStateRule.empty Examples.Fixtures.DualNot.ports
  outputCoverage := by rfl
end Silean.Examples.Fixtures.RepeatedDualNot
