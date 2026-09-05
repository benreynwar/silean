import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

/-- Stateless one-bit AND primitive. -/
@[reducible] def and : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun | .output => inputs .left && inputs .right
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

end Silean.Primitives
