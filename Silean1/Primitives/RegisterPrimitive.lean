import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

/-- One-bit register primitive. It outputs the current stored bit and captures
its input as the next-cycle state. -/
@[reducible] def register : Primitive where
  ports := unaryPorts
  localState := registerStateMap
  outputReads := []
  outputValues := fun _ state => fun | .output => state .stored
  nextStateValues := fun inputs _ => fun | .stored => inputs .input
  outputRespectsReads := by
    intro left right state agrees
    rfl
end Silean.Primitives
