import Silean.Modules.VectorLayout.VectorLayout

/-! # Reusable vector-extension layouts

Specialized configurations of `VectorLayout` and their arithmetic meanings.
They introduce no separate hardware-module boundary.
-/

namespace Silean.Modules.VectorLayout

open Silean

/-- Extend or truncate an LSB-first vector. Signed extension copies the most
significant input bit; unsigned extension fills with zero. A zero-width input
has value zero under either interpretation. -/
def extensionLayout (signed : Bool) : (inputWidth outputWidth : Nat) →
    Fin outputWidth → BitSource inputWidth
  | 0, _ => fun _ => .constant false
  | inputWidth + 1, _ => fun index =>
      if withinInput : index.val < inputWidth + 1 then
        .input ⟨index.val, withinInput⟩
      else if signed then
        .input (Fin.last inputWidth)
      else
        .constant false

/-- Native packed meaning of `extensionLayout`. -/
def extensionValue (signed : Bool) (outputWidth : Nat)
    (input : Fin inputWidth → Bool) : Fin outputWidth → Bool :=
  let packed := BitVector.toBitVec inputWidth input
  BitVector.ofBitVec <|
    if signed then packed.signExtend outputWidth else packed.setWidth outputWidth

/-- Applying the layout is native signed or unsigned width conversion. -/
theorem apply_extensionLayout (signed : Bool) (inputWidth outputWidth : Nat)
    (input : Fin inputWidth → Bool) :
    apply (extensionLayout signed inputWidth outputWidth) input =
      extensionValue signed outputWidth input := by
  funext index
  cases inputWidth with
  | zero =>
      have packedZero : BitVector.toBitVec 0 input = 0#0 :=
        Subsingleton.elim _ _
      rw [extensionValue, packedZero]
      cases signed <;>
        simp [apply, extensionLayout, BitVector.ofBitVec, BitVec.signExtend]
  | succ inputWidth =>
      let packed := BitVector.toBitVec (inputWidth + 1) input
      cases signed with
      | false =>
          change apply (extensionLayout false (inputWidth + 1) outputWidth)
              input index = (packed.setWidth outputWidth)[index.val]
          rw [BitVec.getElem_setWidth]
          by_cases withinInput : index.val < inputWidth + 1
          · rw [BitVec.getLsbD_eq_getElem withinInput]
            simpa [apply, extensionLayout, withinInput, packed] using
              (BitVector.getLsb_toBitVec (inputWidth + 1) input
                ⟨index.val, withinInput⟩).symm
          · rw [BitVec.getLsbD_of_ge packed index.val (by omega)]
            simp [apply, extensionLayout, withinInput]
      | true =>
          change apply (extensionLayout true (inputWidth + 1) outputWidth)
              input index = (packed.signExtend outputWidth)[index.val]
          rw [BitVec.getElem_signExtend index.isLt]
          by_cases withinInput : index.val < inputWidth + 1
          · simpa [apply, extensionLayout, withinInput, packed] using
              (BitVector.getLsb_toBitVec (inputWidth + 1) input
                ⟨index.val, withinInput⟩).symm
          · have signBit : packed.msb = input (Fin.last inputWidth) := by
              rw [BitVec.msb_eq_getLsbD_last]
              simp only [Nat.add_sub_cancel]
              rw [BitVec.getLsbD_eq_getElem (Nat.lt_succ_self inputWidth)]
              simpa [packed] using BitVector.getLsb_toBitVec
                (inputWidth + 1) input (Fin.last inputWidth)
            simp [apply, extensionLayout, withinInput, signBit]

/-- Narrowing a signed two's-complement encoding keeps exactly the encoding at
the smaller width.  This is the reusable bit-level justification for an
explicit wrapping boundary after a wider arithmetic carrier. -/
theorem apply_extensionLayout_encodeSigned_of_le
    (inputWidth outputWidth : Nat) (value : Int)
    (outputLeInput : outputWidth ≤ inputWidth) :
    apply (extensionLayout true inputWidth outputWidth)
        (BitVector.ofBitVec (BitVec.ofInt inputWidth value)) =
      BitVector.ofBitVec (BitVec.ofInt outputWidth value) := by
  rw [apply_extensionLayout]
  simp only [extensionValue, BitVector.toBitVec_ofBitVec, if_true]
  rw [BitVec.signExtend_eq_setWidth_of_le _ outputLeInput]
  apply BitVector.toBitVec_injective outputWidth
  simp only [BitVector.toBitVec_ofBitVec]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have divisorDvd :
      ((2 ^ outputWidth : Nat) : Int) ∣
        ((2 ^ inputWidth : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 outputLeInput
  have inputPowerNonzero :
      ((2 ^ inputWidth : Nat) : Int) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos inputWidth)
  have outputPowerNonnegative :
      (0 : Int) ≤ ((2 ^ outputWidth : Nat) : Int) := by omega
  have remainderNonnegative :
      0 ≤ value % ((2 ^ inputWidth : Nat) : Int) :=
    Int.emod_nonneg _ inputPowerNonzero
  have conversionRaw :=
    Int.toNat_emod remainderNonnegative outputPowerNonnegative
  have outputPowerToNat :
      (((2 ^ outputWidth : Nat) : Int).toNat) = 2 ^ outputWidth :=
    Int.toNat_natCast (2 ^ outputWidth)
  rw [outputPowerToNat] at conversionRaw
  have conversion :
      ((value % ((2 ^ inputWidth : Nat) : Int)) %
          ((2 ^ outputWidth : Nat) : Int)).toNat =
        (value % ((2 ^ inputWidth : Nat) : Int)).toNat %
          2 ^ outputWidth := by
    exact conversionRaw
  rw [← conversion]
  exact congrArg Int.toNat (Int.emod_emod_of_dvd value divisorDvd)

end Silean.Modules.VectorLayout
