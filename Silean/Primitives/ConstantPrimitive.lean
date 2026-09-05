import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

/-- Stateless one-bit constant source. -/
@[reducible] def constant (value : Bool) : Primitive where
  ports := constantPorts
  localState := emptySignalMap
  outputReads := []
  outputValues := fun _ _ => fun | .output => value
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    rfl
end Silean.Primitives
