import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

def xorValue (left right : Bool) : Bool :=
  (left && !right) || (!left && right)

/-- Stateless one-bit XOR primitive. -/
@[reducible] def xor : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun | .output => xorValue (inputs .left) (inputs .right)
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

theorem xor_eq_true_iff (left right : Bool) :
    xorValue left right = true ↔ left ≠ right := by
  cases left <;> cases right <;> simp [xorValue]

theorem xor_toNat_add_twice_and (left right : Bool) :
    (xorValue left right).toNat + 2 * (left && right).toNat =
      left.toNat + right.toNat := by
  cases left <;> cases right <;> decide

end Silean.Primitives
