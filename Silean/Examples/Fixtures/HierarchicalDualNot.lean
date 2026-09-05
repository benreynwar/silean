import Silean.Contracts.Cycle.CycleLayerSchedule
import Silean.Examples.Fixtures.DualNot
import Silean.Primitives.Not

namespace Silean.Examples.Fixtures.HierarchicalDualNot

open Silean

inductive Instance
  | forwardNot
  | backwardNot
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .forwardNot | .backwardNot => Primitives.not.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instancePorts := instancePorts

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .forward => context.instanceOutput .forwardNot .output
    | .backward => context.instanceOutput .backwardNot .output
  instanceInput
    | .forwardNot, .input => context.moduleInput .forward
    | .backwardNot, .input => context.moduleInput .backward

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .forwardNot | .backwardNot => Primitives.notCycleContract

@[reducible] def children : Contracts.Cycle.Certification.Layer.ChildStructures
    body childContracts
  | .forwardNot | .backwardNot => Primitives.notCertified.certifiedStructure

@[reducible] def childStructure :=
  fun name => (children name).moduleStructure

def moduleStructure : ModuleStructure ports :=
  Contracts.Cycle.Certification.Layer.moduleStructure body children

end Silean.Examples.Fixtures.HierarchicalDualNot
