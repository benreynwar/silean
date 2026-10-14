import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

/-- Stateless one-bit inversion primitive. -/
@[reducible] def not : Primitive where
  ports := unaryPorts
  localState := emptySignalMap
  outputReads := [.input]
  outputValues := fun inputs _ => fun | .output => !inputs .input
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .input (by simp)]
end Silean.Primitives
