import Silean.CertifiedSchedule
import Silean.Examples.Fixtures.DualNot
import Silean.Primitives.Not

namespace Silean.Examples.Fixtures.HierarchicalDualNot

open Silean

inductive Instance
  | forwardNot
  | backwardNot
deriving Enumeration

@[reducible] def instances : Instances :=
  EnumeratedMap.of Instance fun
    | .forwardNot | .backwardNot => Primitives.not.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instances := instances

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instances where
  moduleOutput
    | .forward => context.instanceOutput .forwardNot .output
    | .backward => context.instanceOutput .backwardNot .output
  instanceInput
    | .forwardNot, .input => context.moduleInput .forward
    | .backwardNot, .input => context.moduleInput .backward

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def children : Certified.Children body
  | .forwardNot | .backwardNot => Primitives.notCertified

@[reducible] def childStructure := Certified.childStructure children

def moduleStructure : ModuleStructure ports :=
  Certified.moduleStructure body children

end Silean.Examples.Fixtures.HierarchicalDualNot
