import Silean.Modules.PartialProductRow.PartialProductRow

/-! Arithmetic proof support for the public partial-product-row semantics. -/

namespace Silean.Modules.PartialProductRow.Internal

open Silean

theorem resultNat_lt_cardinality
    (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    (multiplicand : Fin multiplicandWidth → Bool) (select : Bool) :
    resultNat multiplicandWidth row multiplicand select <
      BitVector.cardinality (multiplicandWidth + multiplierWidth) := by
  rw [BitVector.cardinality_eq_pow]
  cases select with
  | false =>
      simp only [resultNat]
      exact Nat.pow_pos (by omega)
  | true =>
      simp only [resultNat, if_true, Nat.shiftLeft_eq]
      have multiplicandBound :=
        BitVector.toNat_lt_cardinality multiplicandWidth multiplicand
      rw [BitVector.cardinality_eq_pow] at multiplicandBound
      calc
        BitVector.toNat multiplicandWidth multiplicand * 2 ^ row.val <
            2 ^ multiplicandWidth * 2 ^ row.val :=
          Nat.mul_lt_mul_of_pos_right multiplicandBound (Nat.pow_pos (by omega))
        _ = 2 ^ (multiplicandWidth + row.val) := (Nat.pow_add _ _ _).symm
        _ < 2 ^ (multiplicandWidth + multiplierWidth) :=
          Nat.pow_lt_pow_right (by omega) (by omega)

theorem toNat_resultValue (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    (multiplicand : Fin multiplicandWidth → Bool) (select : Bool) :
    BitVector.toNat (multiplicandWidth + multiplierWidth)
        (resultValue multiplicandWidth multiplierWidth row multiplicand select) =
      resultNat multiplicandWidth row multiplicand select := by
  rw [resultValue, BitVector.toNat_ofNat, Nat.mod_eq_of_lt]
  exact resultNat_lt_cardinality multiplicandWidth multiplierWidth
    row multiplicand select

end Silean.Modules.PartialProductRow.Internal
