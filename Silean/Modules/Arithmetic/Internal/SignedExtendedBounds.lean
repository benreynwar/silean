import Silean.Modules.Arithmetic

/-! Exact range bounds for one-bit-extended signed addition and subtraction. -/

namespace Silean.Modules.Arithmetic.Internal

open Silean

theorem signed_add_bounds_extended (width : Nat)
    (left right : BitVec width) :
    -(2 : Int) ^ width ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < (2 : Int) ^ width := by
  cases width with
  | zero =>
      rw [BitVec.of_length_zero (x := left),
        BitVec.of_length_zero (x := right)]
      simp
  | succ width =>
      have leftLower := BitVec.le_toInt left
      have leftUpper := BitVec.toInt_lt (x := left)
      have rightLower := BitVec.le_toInt right
      have rightUpper := BitVec.toInt_lt (x := right)
      simp only [Nat.add_sub_cancel] at leftLower leftUpper rightLower rightUpper
      rw [Int.pow_succ]
      constructor <;> omega

theorem signed_sub_bounds_extended (width : Nat)
    (left right : BitVec width) :
    -(2 : Int) ^ width ≤ left.toInt - right.toInt ∧
      left.toInt - right.toInt < (2 : Int) ^ width := by
  cases width with
  | zero =>
      rw [BitVec.of_length_zero (x := left),
        BitVec.of_length_zero (x := right)]
      simp
  | succ width =>
      have leftLower := BitVec.le_toInt left
      have leftUpper := BitVec.toInt_lt (x := left)
      have rightLower := BitVec.le_toInt right
      have rightUpper := BitVec.toInt_lt (x := right)
      simp only [Nat.add_sub_cancel] at leftLower leftUpper rightLower rightUpper
      rw [Int.pow_succ]
      constructor <;> omega

end Silean.Modules.Arithmetic.Internal
