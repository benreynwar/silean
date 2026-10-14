import Silean.Modules.Add.Add
import Silean.Modules.AddSub.AddSub
import Silean.Modules.AddSubWithCarry.AddSubWithCarryDerived
import Silean.Modules.AddWithCarry.AddWithCarryDerived
import Silean.Modules.Arithmetic.Internal.ArithmeticTheorems
import Silean.Modules.Sub.Sub

/-! Pure arithmetic bridge from extended low-level children to the natural
contracts of the general arithmetic families. -/

namespace Silean.Modules.Arithmetic.Internal

open Silean

private theorem ofInt_sub (width : Nat) (left right : Int) :
    BitVec.ofInt width left - BitVec.ofInt width right =
      BitVec.ofInt width (left - right) := by
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    Int.sub_eq_add_neg]

theorem addCircuitResult_eq_resultValue (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    let width := resultWidth leftWidth rightWidth extendOutput
    AddWithCarry.resultValue width
        (VectorLayout.apply
          (VectorLayout.extensionLayout leftSigned leftWidth width) left)
        (VectorLayout.apply
          (VectorLayout.extensionLayout rightSigned rightWidth width) right)
        false =
      Add.resultValue leftWidth rightWidth leftSigned rightSigned extendOutput
        left right := by
  dsimp only
  apply BitVector.toBitVec_injective
  rw [AddWithCarry.toBitVec_resultValue_noCarry]
  rw [toBitVec_apply_extensionLayout_eq_ofInt,
    toBitVec_apply_extensionLayout_eq_ofInt]
  rw [Add.resultValue, encode, BitVector.toBitVec_ofBitVec]
  exact (BitVec.ofInt_add
    (operandValue leftSigned leftWidth left)
    (operandValue rightSigned rightWidth right)).symm

theorem subCircuitResult_eq_resultValue (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    let width := resultWidth leftWidth rightWidth extendOutput
    (AddSubWithCarry.addSubBits width
      (VectorLayout.apply
        (VectorLayout.extensionLayout leftSigned leftWidth width) left)
      (VectorLayout.apply
        (VectorLayout.extensionLayout rightSigned rightWidth width) right)
      true).1 =
      Sub.resultValue leftWidth rightWidth leftSigned rightSigned extendOutput
        left right := by
  dsimp only
  apply BitVector.toBitVec_injective
  rw [AddSubWithCarry.toBitVec_addSubBits_result]
  rw [toBitVec_apply_extensionLayout_eq_ofInt,
    toBitVec_apply_extensionLayout_eq_ofInt]
  rw [Sub.resultValue, encode, BitVector.toBitVec_ofBitVec]
  exact ofInt_sub _ _ _

theorem addSubCircuitResult_eq_resultValue (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool)
    (subtract : Bool) :
    let width := resultWidth leftWidth rightWidth extendOutput
    (AddSubWithCarry.addSubBits width
      (VectorLayout.apply
        (VectorLayout.extensionLayout leftSigned leftWidth width) left)
      (VectorLayout.apply
        (VectorLayout.extensionLayout rightSigned rightWidth width) right)
      subtract).1 =
      AddSub.resultValue leftWidth rightWidth leftSigned rightSigned extendOutput
        left right subtract := by
  dsimp only
  apply BitVector.toBitVec_injective
  rw [AddSubWithCarry.toBitVec_addSubBits_result]
  rw [toBitVec_apply_extensionLayout_eq_ofInt,
    toBitVec_apply_extensionLayout_eq_ofInt]
  rw [AddSub.resultValue, encode, BitVector.toBitVec_ofBitVec]
  cases subtract
  · exact (BitVec.ofInt_add
      (operandValue leftSigned leftWidth left)
      (operandValue rightSigned rightWidth right)).symm
  · exact ofInt_sub _ _ _

end Silean.Modules.Arithmetic.Internal
