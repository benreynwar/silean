import Silean.Modules.Arithmetic
import Silean.Modules.VectorLayout.Extensions

/-! Arithmetic meaning of reusable structural width conversions. -/

namespace Silean.Modules.Arithmetic.Internal

open Silean

theorem leftWidth_le_resultWidth (leftWidth rightWidth : Nat)
    (extendOutput : Bool) :
    leftWidth ≤ resultWidth leftWidth rightWidth extendOutput := by
  cases extendOutput <;> simp [resultWidth] <;> omega

theorem rightWidth_le_resultWidth (leftWidth rightWidth : Nat)
    (extendOutput : Bool) :
    rightWidth ≤ resultWidth leftWidth rightWidth extendOutput := by
  cases extendOutput <;> simp [resultWidth] <;> omega

/-- Extending according to the selected interpretation produces exactly the
destination-width encoding of the operand's natural integer value. -/
theorem toBitVec_extensionValue_eq_ofInt (signed : Bool)
    (inputWidth outputWidth : Nat) (input : Fin inputWidth → Bool) :
    BitVector.toBitVec outputWidth
        (VectorLayout.extensionValue signed outputWidth input) =
      BitVec.ofInt outputWidth (operandValue signed inputWidth input) := by
  cases signed with
  | false =>
      simp only [VectorLayout.extensionValue, operandValue, Bool.false_eq_true,
        if_false, BitVector.toBitVec_ofBitVec]
      exact (BitVec.ofNat_toNat outputWidth
        (BitVector.toBitVec inputWidth input)).symm
  | true =>
      simp [VectorLayout.extensionValue, operandValue, BitVec.signExtend]

/-- The actual layout therefore has the same arithmetic encoding. -/
theorem toBitVec_apply_extensionLayout_eq_ofInt (signed : Bool)
    (inputWidth outputWidth : Nat) (input : Fin inputWidth → Bool) :
    BitVector.toBitVec outputWidth
        (VectorLayout.apply
          (VectorLayout.extensionLayout signed inputWidth outputWidth) input) =
      BitVec.ofInt outputWidth (operandValue signed inputWidth input) := by
  rw [VectorLayout.apply_extensionLayout]
  exact toBitVec_extensionValue_eq_ofInt signed inputWidth outputWidth input

end Silean.Modules.Arithmetic.Internal
