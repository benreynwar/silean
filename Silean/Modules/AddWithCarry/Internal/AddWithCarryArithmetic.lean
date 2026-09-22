import Silean.Modules.AddWithCarry.AddWithCarry

/-! Ripple-recursive arithmetic used only to verify the generated adder. -/

namespace Silean.Modules.AddWithCarry.Internal

open Silean

def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

def addBits : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → (Fin width → Bool) × Bool
  | 0, _, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, left, right, carry =>
      let lower := addBits width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) carry
      let high := sumBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      let carryOut := carryBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

private theorem sumBit_add_twice_carryBit (left right carry : Bool) :
    (sumBit left right carry).toNat + 2 * (carryBit left right carry).toNat =
      left.toNat + right.toNat + carry.toNat := by
  cases left <;> cases right <;> cases carry <;> decide

@[simp] private theorem toNat_lastCases (width : Nat) (high : Bool)
    (lower : Fin width → Bool) :
    BitVector.toNat (width + 1) (Fin.lastCases high lower) =
      (if high then BitVector.cardinality width else 0) +
        BitVector.toNat width lower := by
  simp [BitVector.toNat]

theorem addBits_numeric : ∀ (width : Nat) (left right : Fin width → Bool)
    (carry : Bool),
    BitVector.toNat width (addBits width left right carry).1 +
        BitVector.cardinality width * (addBits width left right carry).2.toNat =
      BitVector.toNat width left + BitVector.toNat width right + carry.toNat
  | 0, _, _, carry => by simp [addBits, BitVector.toNat, BitVector.cardinality]
  | width + 1, left, right, carry => by
      have lower := addBits_numeric width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) carry
      have high := sumBit_add_twice_carryBit
        (left (Fin.last width)) (right (Fin.last width))
        (addBits width (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).2
      have leftBound := BitVector.toNat_lt_cardinality width
        (fun index => left index.castSucc)
      have rightBound := BitVector.toNat_lt_cardinality width
        (fun index => right index.castSucc)
      have resultBound := BitVector.toNat_lt_cardinality width
        (addBits width (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).1
      have lowerResultEta :
          (fun index => (addBits width (fun index => left index.castSucc)
            (fun index => right index.castSucc) carry).1 index) =
          (addBits width (fun index => left index.castSucc)
            (fun index => right index.castSucc) carry).1 := rfl
      rw [BitVector.cardinality_eq_pow] at lower ⊢
      rw [BitVector.cardinality_eq_pow] at leftBound rightBound resultBound
      cases leftHigh : left (Fin.last width) <;>
        cases rightHigh : right (Fin.last width) <;>
        cases lowerCarry : (addBits width
          (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).2 <;>
        simp [addBits, BitVector.toNat, leftHigh, rightHigh, lowerCarry,
          lowerResultEta, sumBit, carryBit,
          Primitives.xorValue] at lower high ⊢ <;>
        omega

theorem addBits_result (width : Nat) (left right : Fin width → Bool)
    (carry : Bool) :
    (addBits width left right carry).1 =
      resultValue width left right carry := by
  apply BitVector.toNat_injective width
  rw [resultValue, BitVector.toNat_ofNat]
  have equation := addBits_numeric width left right carry
  have resultBound := BitVector.toNat_lt_cardinality width
    (addBits width left right carry).1
  unfold totalValue
  rw [BitVector.cardinality_eq_pow] at equation resultBound ⊢
  cases carryOut : (addBits width left right carry).2 <;>
    simp [carryOut] at equation
  · rw [← equation, Nat.mod_eq_of_lt resultBound]
  · rw [← equation]
    simp [Nat.mod_eq_of_lt resultBound]

theorem addBits_carry (width : Nat) (left right : Fin width → Bool)
    (carry : Bool) :
    (addBits width left right carry).2 =
      carryValue width left right carry := by
  have equation := addBits_numeric width left right carry
  have resultBound := BitVector.toNat_lt_cardinality width
    (addBits width left right carry).1
  unfold carryValue totalValue
  rw [BitVector.cardinality_eq_pow] at equation resultBound
  cases carryOut : (addBits width left right carry).2 with
  | false =>
      simp [carryOut] at equation
      rw [← equation]
      exact (Nat.testBit_lt_two_pow resultBound).symm
  | true =>
      simp [carryOut] at equation
      have lower : 2 ^ width ≤
          BitVector.toNat width left + BitVector.toNat width right +
            carry.toNat := by
        omega
      have upper :
          BitVector.toNat width left + BitVector.toNat width right +
              carry.toNat < 2 ^ (width + 1) := by
        rw [Nat.pow_succ]
        omega
      exact (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt lower upper).symm

theorem naturalValues_numeric (width : Nat)
    (left right : Fin width → Bool) (carry : Bool) :
    BitVector.toNat width (resultValue width left right carry) +
        BitVector.cardinality width *
          (carryValue width left right carry).toNat =
      totalValue width left right carry := by
  rw [← addBits_result width left right carry,
    ← addBits_carry width left right carry]
  exact addBits_numeric width left right carry

end Silean.Modules.AddWithCarry.Internal
