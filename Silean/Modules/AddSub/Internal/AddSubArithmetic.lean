import Silean.Modules.AddSub.AddSub
import Silean.Modules.Add.Internal.AddArithmetic

namespace Silean.Modules.AddSub.Internal

open Silean

private theorem addBits_transformed : ∀ (width : Nat)
    (left right : Fin width → Bool) (subtract chain : Bool),
    Add.Internal.addBits width left
        (fun index => Primitives.xorValue (right index) subtract)
        (if subtract then !chain else chain) =
      operate width left right subtract chain
  | 0, _, _, subtract, chain => by simp [Add.Internal.addBits, operate]
  | width + 1, left, right, subtract, chain => by
      have lower := addBits_transformed width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      simp only [Add.Internal.addBits, operate]
      rw [lower]
      cases lowerOp : operate width (fun index => left index.castSucc)
          (fun index => right index.castSucc) subtract chain with
      | mk lowerBits lowerFlag =>
          cases subtract <;> cases lowerFlag <;>
            cases leftHigh : left (Fin.last width) <;>
            cases rightHigh : right (Fin.last width) <;>
            simp [Add.Internal.sumBit, Add.Internal.carryBit,
              sumBit, carryBit, borrowBit,
              Primitives.xorValue]

theorem addBits_xorRight_eq_addSubBits (width : Nat)
    (left right : Fin width → Bool) (subtract : Bool) :
    Add.Internal.addBits width left
        (fun index => Primitives.xorValue (right index) subtract) subtract =
      addSubBits width left right subtract := by
  simpa [addSubBits] using addBits_transformed width left right subtract false

private theorem complemented_toNat : ∀ (width : Nat) (value : Fin width → Bool),
    BitVector.toNat width (fun index => Primitives.xorValue (value index) true) +
        BitVector.toNat width value + 1 = BitVector.cardinality width
  | 0, _ => by simp [BitVector.toNat, BitVector.cardinality]
  | width + 1, value => by
      have lower := complemented_toNat width (fun index => value index.castSucc)
      cases high : value (Fin.last width) <;>
        simp [BitVector.toNat, BitVector.cardinality, high,
          Primitives.xorValue] at lower ⊢ <;>
        omega

theorem addSubBits_result_toNat (width : Nat) (left right : Fin width → Bool)
    (subtract : Bool) :
    BitVector.toNat width (addSubBits width left right subtract).1 =
      if subtract then
        (BitVector.toNat width left + BitVector.cardinality width -
          BitVector.toNat width right) % BitVector.cardinality width
      else
        (BitVector.toNat width left + BitVector.toNat width right) %
          BitVector.cardinality width := by
  have equation := Add.Internal.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) subtract) subtract
  rw [addBits_xorRight_eq_addSubBits] at equation
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right subtract).1
  have resultBoundPow :
      BitVector.toNat width (addSubBits width left right subtract).1 < 2 ^ width := by
    simpa using resultBound
  cases subtract with
  | false =>
      simp [Primitives.xorValue] at equation ⊢
      rw [← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]
  | true =>
      have complement := complemented_toNat width right
      have rightBound := BitVector.toNat_lt_cardinality width right
      simp at equation ⊢
      rw [BitVector.cardinality_eq_pow] at complement rightBound
      have transformedSum :
          BitVector.toNat width left +
              BitVector.toNat width
                (fun index => Primitives.xorValue (right index) true) + 1 =
            BitVector.toNat width left + 2 ^ width -
              BitVector.toNat width right := by
        omega
      rw [← transformedSum, ← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]

theorem addSubBits_carry_subtract (width : Nat)
    (left right : Fin width → Bool) :
    (addSubBits width left right true).2 =
      decide (BitVector.toNat width right ≤ BitVector.toNat width left) := by
  have equation := Add.Internal.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) true) true
  rw [addBits_xorRight_eq_addSubBits] at equation
  have complement := complemented_toNat width right
  have leftBound := BitVector.toNat_lt_cardinality width left
  have rightBound := BitVector.toNat_lt_cardinality width right
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right true).1
  rw [BitVector.cardinality_eq_pow] at complement leftBound rightBound resultBound
  cases carry : (addSubBits width left right true).2 <;>
    by_cases noBorrow : BitVector.toNat width right ≤ BitVector.toNat width left <;>
    simp [carry, noBorrow] at equation ⊢ <;>
    omega

end Silean.Modules.AddSub.Internal
