import Silean.Modules.CarrySaveAdder.CarrySaveAdder
import Silean.Modules.FullAdder.FullAdder

/-! Arithmetic proof support for the public carry-save semantics. -/

namespace Silean.Modules.CarrySaveAdder.Internal

open Silean

/-- The unshifted carry bits used internally by the structural proof. -/
def rawCarryValue (width : Nat) (iA iB iC : Fin width → Bool) :
    Fin width → Bool :=
  fun index => carryBit (iA index) (iB index) (iC index)

theorem fullAdder_sumValue_eq_sumBit (iA iB iC : Bool) :
    FullAdder.sumValue iA iB iC = sumBit iA iB iC := by
  cases iA <;> cases iB <;> cases iC <;> decide

theorem fullAdder_carryValue_eq_carryBit (iA iB iC : Bool) :
    FullAdder.carryValue iA iB iC = carryBit iA iB iC := by
  cases iA <;> cases iB <;> cases iC <;> decide

private theorem bit_numeric (iA iB iC : Bool) :
    (sumBit iA iB iC).toNat + 2 * (carryBit iA iB iC).toNat =
      iA.toNat + iB.toNat + iC.toNat := by
  cases iA <;> cases iB <;> cases iC <;> decide

/-- Before the carry vector is shifted and truncated, its doubled numerical
value and the sum vector exactly equal the three input values. -/
theorem sum_add_twice_rawCarry : ∀ (width : Nat)
    (iA iB iC : Fin width → Bool),
    BitVector.toNat width (sumValue width iA iB iC) +
        2 * BitVector.toNat width (rawCarryValue width iA iB iC) =
      totalValue width iA iB iC
  | 0, _, _, _ => by
      simp [BitVector.toNat, totalValue]
  | width + 1, iA, iB, iC => by
      let lowerA := fun index : Fin width => iA index.castSucc
      let lowerB := fun index : Fin width => iB index.castSucc
      let lowerC := fun index : Fin width => iC index.castSucc
      have lower := sum_add_twice_rawCarry width lowerA lowerB lowerC
      simp only [totalValue] at lower
      have high := bit_numeric
        (iA (Fin.last width)) (iB (Fin.last width)) (iC (Fin.last width))
      change
        ((if sumBit (iA (Fin.last width))
              (iB (Fin.last width)) (iC (Fin.last width)) then
            BitVector.cardinality width else 0) +
          BitVector.toNat width (sumValue width lowerA lowerB lowerC)) +
            2 *
              ((if carryBit (iA (Fin.last width))
                    (iB (Fin.last width)) (iC (Fin.last width)) then
                  BitVector.cardinality width else 0) +
                BitVector.toNat width
                  (rawCarryValue width lowerA lowerB lowerC)) =
          ((if iA (Fin.last width) then BitVector.cardinality width else 0) +
              BitVector.toNat width lowerA) +
            ((if iB (Fin.last width) then BitVector.cardinality width else 0) +
              BitVector.toNat width lowerB) +
            ((if iC (Fin.last width) then BitVector.cardinality width else 0) +
              BitVector.toNat width lowerC)
      cases iAHigh : iA (Fin.last width) <;>
        cases iBHigh : iB (Fin.last width) <;>
        cases iCHigh : iC (Fin.last width) <;>
        simp [iAHigh, iBHigh, iCHigh, sumBit, carryBit] at high ⊢ <;>
        omega

private theorem carryValue_eq_ofNat_shift (width : Nat)
    (iA iB iC : Fin width → Bool) :
    carryValue width iA iB iC =
      BitVector.ofNat width
        (BitVector.toNat width (rawCarryValue width iA iB iC) <<< 1) := by
  funext index
  unfold carryValue BitVector.ofNat
  simp only [Nat.testBit_shiftLeft]
  by_cases nonzero : 0 < index.val
  · have one_le : 1 ≤ index.val := by omega
    simp only [nonzero, dite_true, one_le, decide_true]
    simpa [rawCarryValue] using (BitVector.testBit_toNat width
      (rawCarryValue width iA iB iC)
      ⟨index.val - 1, by omega⟩).symm
  · have zero : index.val = 0 := by omega
    simp [zero]

/-- The public carry output is the doubled raw carry value reduced to the
fixed output width. -/
theorem toNat_carryValue (width : Nat) (iA iB iC : Fin width → Bool) :
    BitVector.toNat width (carryValue width iA iB iC) =
      (2 * BitVector.toNat width (rawCarryValue width iA iB iC)) %
        BitVector.cardinality width := by
  rw [carryValue_eq_ofNat_shift, BitVector.toNat_ofNat, Nat.shiftLeft_eq]
  congr 1
  omega

/-- The two fixed-width outputs preserve the three-input value modulo the
vector width. -/
theorem outputs_numeric_modulo (width : Nat)
    (iA iB iC : Fin width → Bool) :
    (BitVector.toNat width (sumValue width iA iB iC) +
        BitVector.toNat width (carryValue width iA iB iC)) %
        BitVector.cardinality width =
      totalValue width iA iB iC % BitVector.cardinality width := by
  rw [toNat_carryValue]
  have exact := sum_add_twice_rawCarry width iA iB iC
  rw [← exact]
  simp [Nat.add_mod]

end Silean.Modules.CarrySaveAdder.Internal
