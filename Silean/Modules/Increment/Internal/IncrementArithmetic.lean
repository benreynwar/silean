import Silean.Modules.Increment.Increment

namespace Silean.Modules.Increment.Internal

open Silean

@[simp] private theorem toNat_lastCases (width : Nat) (high : Bool)
    (lower : Fin width → Bool) :
    BitVector.toNat (width + 1) (Fin.lastCases high lower) =
      (if high then BitVector.cardinality width else 0) +
        BitVector.toNat width lower := by
  simp [BitVector.toNat]

private theorem addCarry_numeric : ∀ (width : Nat) (bits : Fin width → Bool)
    (carry : Bool),
    BitVector.toNat width (addCarry width bits carry).1 +
        BitVector.cardinality width * (addCarry width bits carry).2.toNat =
      BitVector.toNat width bits + carry.toNat
  | 0, _, carry => by simp [addCarry, BitVector.toNat, BitVector.cardinality]
  | width + 1, bits, carry => by
      have lower := addCarry_numeric width
        (fun index => bits index.castSucc) carry
      have cardinalityPositive : 0 < BitVector.cardinality width := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.pow_pos (by omega)
      rw [BitVector.cardinality_eq_pow] at lower cardinalityPositive ⊢
      have lowerResultEta :
          (fun index => (addCarry width
            (fun index => bits index.castSucc) carry).1 index) =
          (addCarry width (fun index => bits index.castSucc) carry).1 := rfl
      cases highValue : bits (Fin.last width) <;>
        cases lowerCarry : (addCarry width
          (fun index => bits index.castSucc) carry).2 <;>
        simp [addCarry, BitVector.toNat,
          highValue, lowerCarry, lowerResultEta,
          HalfAdder.sumValue, HalfAdder.carryValue,
          Primitives.xorValue] at lower ⊢ <;>
        omega

theorem incrementValue_toNat (width : Nat) (bits : Fin width → Bool) :
    BitVector.toNat width (incrementValue width bits) =
      (BitVector.toNat width bits + 1) % BitVector.cardinality width := by
  have equation := addCarry_numeric width bits true
  simp at equation
  have bound := BitVector.toNat_lt_cardinality width (incrementValue width bits)
  have bound' : BitVector.toNat width (addCarry width bits true).1 < 2 ^ width := by
    simpa [incrementValue, BitVector.cardinality_eq_pow] using bound
  change BitVector.toNat width (addCarry width bits true).1 = _
  rw [← equation]
  simp [Nat.mod_eq_of_lt bound']

end Silean.Modules.Increment.Internal
