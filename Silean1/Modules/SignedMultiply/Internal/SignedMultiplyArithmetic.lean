import Silean.Modules.SignedMultiply.Internal.SignedMultiplyStructure

/-! Arithmetic support connecting the sign/magnitude data path to the direct
native signed-product contract. -/

namespace Silean.Modules.SignedMultiply.Internal

open Silean

/-- The implementation's one-bit layout returns native `BitVec.msb`, including
the false sign of a zero-width vector. -/
theorem signLayout_apply (width : Nat) (value : Fin width → Bool) :
    VectorLayout.apply (SignedMultiply.signLayout width) value 0 =
      (BitVector.toBitVec width value).msb := by
  cases width with
  | zero =>
      simp [SignedMultiply.signLayout, VectorLayout.apply, BitVec.msb]
  | succ width =>
      have bit := congrFun
        (BitVector.ofBitVec_toBitVec (width + 1) value) (Fin.last width)
      change (BitVector.toBitVec (width + 1) value)[width] =
        value (Fin.last width) at bit
      rw [BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_eq_getElem (by omega)]
      simp [SignedMultiply.signLayout, VectorLayout.apply]
      let index : Fin (width + 1) := ⟨width, by omega⟩
      have index_eq : index = Fin.last width := Fin.ext rfl
      change value index = (BitVector.toBitVec (width + 1) value)[width]
      rw [index_eq]
      exact bit.symm

private theorem toInt_eq_signed_absNat {width : Nat} (value : BitVec width) :
    value.toInt =
      bif value.msb then -(value.abs.toNat : Int) else value.abs.toNat := by
  cases sign : value.msb with
  | false =>
      simp [sign, BitVec.abs_eq, BitVec.toInt_eq_toNat_of_msb sign]
  | true =>
      rw [BitVec.toInt_eq_msb_cond, BitVec.toNat_abs]
      simp [sign]
      have bound := value.isLt
      rw [Int.ofNat_sub (Nat.le_of_lt bound), Int.neg_sub,
        Int.natCast_pow, Int.cast_ofNat_Int]

/-- Sign/magnitude multiplication followed by conditional negation is exactly
native full-width signed multiplication, including minimum signed operands. -/
theorem signed_product_algorithm {leftWidth rightWidth : Nat}
    (left : BitVec leftWidth) (right : BitVec rightWidth) :
    (bif Primitives.xorValue left.msb right.msb then
      -BitVec.ofNat (leftWidth + rightWidth)
        (left.abs.toNat * right.abs.toNat)
    else
      BitVec.ofNat (leftWidth + rightWidth)
        (left.abs.toNat * right.abs.toNat)) =
      BitVec.ofInt (leftWidth + rightWidth) (left.toInt * right.toInt) := by
  have leftInt := toInt_eq_signed_absNat left
  have rightInt := toInt_eq_signed_absNat right
  cases leftSign : left.msb <;> cases rightSign : right.msb <;>
    simp [leftSign, rightSign, Primitives.xorValue] at leftInt rightInt ⊢
  case false.false =>
    rw [leftInt, rightInt, ← Int.natCast_mul, BitVec.ofInt_natCast]
  case false.true =>
    rw [leftInt, rightInt, Int.mul_neg,
      BitVec.neg_ofNat_eq_ofInt_neg, Int.natCast_mul]
  case true.false =>
    rw [leftInt, rightInt, Int.neg_mul,
      BitVec.neg_ofNat_eq_ofInt_neg, Int.natCast_mul]
  case true.true =>
    rw [leftInt, rightInt, Int.neg_mul_neg, ← Int.natCast_mul,
      BitVec.ofInt_natCast]

/-- The product of independently sized signed vectors fits exactly in their
combined signed width. -/
theorem product_bounds (leftWidth rightWidth : Nat)
    (left : BitVec leftWidth) (right : BitVec rightWidth) :
    -2 ^ (leftWidth + rightWidth - 1) ≤ left.toInt * right.toInt ∧
      left.toInt * right.toInt < 2 ^ (leftWidth + rightWidth - 1) := by
  cases leftWidth with
  | zero =>
      rw [BitVec.of_length_zero (x := left)]
      simp only [BitVec.toInt_zero, Int.zero_mul]
      have positive : 0 < (2 : Int) ^ (0 + rightWidth - 1) :=
        Int.pow_pos (by omega)
      constructor <;> omega
  | succ leftWidth =>
      cases rightWidth with
      | zero =>
          rw [BitVec.of_length_zero (x := right)]
          simp only [BitVec.toInt_zero, Int.mul_zero]
          have positive : 0 < (2 : Int) ^ (leftWidth + 1 + 0 - 1) :=
            Int.pow_pos (by omega)
          constructor <;> omega
      | succ rightWidth =>
          let leftBound : Nat := 2 ^ leftWidth
          let rightBound : Nat := 2 ^ rightWidth
          have leftLower : -(leftBound : Int) ≤ left.toInt := by
            simpa [leftBound] using BitVec.le_toInt left
          have leftUpper : left.toInt < leftBound := by
            simpa [leftBound] using (BitVec.toInt_lt (x := left))
          have rightLower : -(rightBound : Int) ≤ right.toInt := by
            simpa [rightBound] using BitVec.le_toInt right
          have rightUpper : right.toInt < rightBound := by
            simpa [rightBound] using (BitVec.toInt_lt (x := right))
          have lower : -((leftBound * rightBound : Nat) : Int) ≤
              left.toInt * right.toInt :=
            Int.neg_mul_le_mul leftLower leftUpper rightLower rightUpper
          have upper : left.toInt * right.toInt ≤
              ((leftBound * rightBound : Nat) : Int) := by
            by_cases minimum : right.toInt = -(rightBound : Int)
            · rw [minimum]
              have positive : 0 ≤ (rightBound : Int) := by omega
              have scaled := Int.mul_le_mul_of_nonneg_right leftLower positive
              calc
                left.toInt * -(rightBound : Int) =
                    -(left.toInt * (rightBound : Int)) :=
                  Int.mul_neg _ _
                _ ≤ -(-(leftBound : Int) * (rightBound : Int)) :=
                  Int.neg_le_neg scaled
                _ = (leftBound : Int) * (rightBound : Int) := by
                  rw [Int.neg_mul, Int.neg_neg]
                _ = ((leftBound * rightBound : Nat) : Int) := by
                  rw [Int.natCast_mul]
            · have negLower : -(rightBound : Int) ≤ -right.toInt := by omega
              have negUpper : -right.toInt < (rightBound : Int) := by omega
              have bound := Int.neg_mul_le_mul leftLower leftUpper
                negLower negUpper
              rw [Int.mul_neg] at bound
              omega
          have productPower : leftBound * rightBound =
              2 ^ (leftWidth + rightWidth) := by
            simp [leftBound, rightBound, Nat.pow_add]
          rw [productPower] at lower upper
          simp only [Int.natCast_pow, Int.cast_ofNat_Int] at lower upper
          have resultPower :
              (2 : Int) ^ ((leftWidth + 1) + (rightWidth + 1) - 1) =
                2 * (2 : Int) ^ (leftWidth + rightWidth) := by
            rw [show (leftWidth + 1) + (rightWidth + 1) - 1 =
              leftWidth + rightWidth + 1 by omega, Int.pow_succ]
            omega
          have positivePower : 0 < (2 : Int) ^ (leftWidth + rightWidth) :=
            Int.pow_pos (by omega)
          rw [resultPower]
          constructor <;> omega

/-- Decoding the contract result gives exact integer multiplication rather
than a wrapped product. -/
theorem resultValue_toInt (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (SignedMultiply.resultValue leftWidth rightWidth left right)).toInt =
      (BitVector.toBitVec leftWidth left).toInt *
        (BitVector.toBitVec rightWidth right).toInt := by
  rw [SignedMultiply.resultValue, BitVector.toBitVec_ofBitVec]
  by_cases positive : 0 < leftWidth + rightWidth
  · have bounds := product_bounds leftWidth rightWidth
      (BitVector.toBitVec leftWidth left)
      (BitVector.toBitVec rightWidth right)
    exact BitVec.toInt_ofInt_eq_self positive bounds.1 bounds.2
  · have leftZero : leftWidth = 0 := by omega
    have rightZero : rightWidth = 0 := by omega
    subst leftWidth
    subst rightWidth
    rw [BitVec.toInt_zero_length, BitVec.toInt_zero_length]
    rfl

end Silean.Modules.SignedMultiply.Internal
