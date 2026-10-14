import Silean.Modules.ConditionalNegate.ConditionalNegate

/-! Arithmetic bridge from the XOR-plus-add construction to native fixed-width
negation. -/

namespace Silean.Modules.ConditionalNegate.Internal

open Silean

private theorem xor_true_eq_not (width : Nat) (value : Fin width → Bool) :
    (fun index => Primitives.xorValue (value index) true) =
      BitVector.ofBitVec (~~~BitVector.toBitVec width value) := by
  funext index
  have bit := congrFun (BitVector.ofBitVec_toBitVec width value) index
  change (BitVector.toBitVec width value)[index.val] = value index at bit
  simp [BitVector.ofBitVec, Primitives.xorValue, bit]

/-- The XOR-plus-add data path computes the contract's native fixed-width
conditional negation. -/
theorem add_result_eq_resultValue (width : Nat)
    (value : Fin width → Bool) (negate : Bool) :
    AddWithCarry.resultValue width
        (fun index => Primitives.xorValue (value index) negate)
        (fun _ => false) negate =
      resultValue width value negate := by
  cases negate with
  | false =>
      apply BitVector.toNat_injective width
      simp only [AddWithCarry.resultValue, AddWithCarry.totalValue,
        Primitives.xorValue,
        Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
        BitVector.toNat_false, Bool.toNat_false, Nat.add_zero,
        BitVector.toNat_ofNat]
      change BitVector.toNat width value % BitVector.cardinality width =
        BitVector.toNat width value
      rw [Nat.mod_eq_of_lt (BitVector.toNat_lt_cardinality width value)]
  | true =>
      rw [xor_true_eq_not]
      apply BitVector.toNat_injective width
      simp only [AddWithCarry.resultValue, AddWithCarry.totalValue,
        BitVector.toNat_ofBitVec,
        BitVec.toNat_not, BitVector.toNat_false, Bool.toNat_true, Nat.add_zero,
        BitVector.toNat_ofNat]
      rw [resultValue]
      simp only [cond_true]
      rw [BitVector.toNat_ofBitVec]
      change (2 ^ width - 1 - (BitVector.toBitVec width value).toNat + 1) %
          BitVector.cardinality width =
        (-BitVector.toBitVec width value).toNat
      rw [BitVec.toNat_neg, BitVector.toBitVec_toNat,
        BitVector.cardinality_eq_pow]
      have bound := BitVector.toNat_lt_cardinality width value
      rw [BitVector.cardinality_eq_pow] at bound
      congr 1
      omega

end Silean.Modules.ConditionalNegate.Internal
