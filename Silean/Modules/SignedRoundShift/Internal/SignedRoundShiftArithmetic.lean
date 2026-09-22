import Mathlib.Tactic
import Silean.Modules.Any.Any
import Silean.Modules.Increment.IncrementDerived
import Silean.Modules.SignedRoundShift.SignedRoundShift
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice

/-! Pure bit-vector arithmetic connecting the guard/sticky implementation to
the signed nearest-even contract. -/

namespace Silean.Modules.SignedRoundShift.Internal

open Silean

/-- Select the highest discarded bit, or false when no bits are discarded. -/
def guardLayout (retainedWidth discardedWidth : Nat) :
    Fin 1 → VectorLayout.BitSource (discardedWidth + retainedWidth) :=
  fun _ =>
    if positive : 0 < discardedWidth then
      .input ⟨discardedWidth - 1, by omega⟩
    else
      .constant false

/-- Retain every discarded bit below the guard bit and replace the guard
position itself with false. This uniform width also covers zero discarded
bits. -/
def stickyLayout (retainedWidth discardedWidth : Nat) :
    Fin discardedWidth →
      VectorLayout.BitSource (discardedWidth + retainedWidth) :=
  fun index =>
    if index.val + 1 < discardedWidth then
      .input ⟨index.val, by omega⟩
    else
      .constant false

/-- Select the least-significant retained bit, or false for a zero-width
result. -/
def retainedLsbLayout (retainedWidth discardedWidth : Nat) :
    Fin 1 → VectorLayout.BitSource (discardedWidth + retainedWidth) :=
  fun _ =>
    if positive : 0 < retainedWidth then
      .input ⟨discardedWidth, by omega⟩
    else
      .constant false

def retainedBits (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    Fin retainedWidth → Bool :=
  VectorSlice.slice (prefixWidth := discardedWidth)
    (width := retainedWidth) (suffixWidth := 0) value

def discardedBits (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    Fin discardedWidth → Bool :=
  fun index => value ⟨index.val, by omega⟩

def guardBit (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) : Bool :=
  VectorLayout.apply (guardLayout retainedWidth discardedWidth) value 0

def stickyBit (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) : Bool :=
  Any.some discardedWidth
    (VectorLayout.apply (stickyLayout retainedWidth discardedWidth) value)

def retainedLsbBit (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) : Bool :=
  VectorLayout.apply
    (retainedLsbLayout retainedWidth discardedWidth) value 0

def roundUp (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) : Bool :=
  guardBit retainedWidth discardedWidth value &&
    (stickyBit retainedWidth discardedWidth value ||
      retainedLsbBit retainedWidth discardedWidth value)

def circuitResult (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    Fin retainedWidth → Bool :=
  bif roundUp retainedWidth discardedWidth value then
    Increment.incrementValue retainedWidth
      (retainedBits retainedWidth discardedWidth value)
  else
    retainedBits retainedWidth discardedWidth value

theorem toBitVec_incrementValue (width : Nat) (value : Fin width → Bool) :
    BitVector.toBitVec width (Increment.incrementValue width value) =
      BitVector.toBitVec width value + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [Increment.incrementValue_toNat, BitVector.cardinality_eq_pow]

@[simp] theorem retainedBits_apply (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool)
    (index : Fin retainedWidth) :
    retainedBits retainedWidth discardedWidth value index =
      value ⟨discardedWidth + index.val, by omega⟩ := by
  change value (Fin.natAdd discardedWidth index) = _
  apply congrArg value
  apply Fin.ext
  rfl

@[simp] theorem discardedBits_apply (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool)
    (index : Fin discardedWidth) :
    discardedBits retainedWidth discardedWidth value index =
      value ⟨index.val, by omega⟩ := rfl

theorem toBitVec_discardedBits (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    BitVector.toBitVec discardedWidth
        (discardedBits retainedWidth discardedWidth value) =
      (BitVector.toBitVec (discardedWidth + retainedWidth) value).extractLsb'
        0 discardedWidth := by
  apply BitVec.eq_of_getElem_eq
  intro index inBounds
  rw [BitVec.getElem_extractLsb' inBounds]
  rw [BitVec.getLsbD_eq_getElem (by omega)]
  calc
    (BitVector.toBitVec discardedWidth
        (discardedBits retainedWidth discardedWidth value))[index] =
        discardedBits retainedWidth discardedWidth value
          ⟨index, inBounds⟩ :=
      BitVector.getLsb_toBitVec _ _ _
    _ = value ⟨index, by omega⟩ := rfl
    _ = (BitVector.toBitVec (discardedWidth + retainedWidth) value)[0 + index] := by
      simpa using (BitVector.getLsb_toBitVec
        (discardedWidth + retainedWidth) value ⟨index, by omega⟩).symm

theorem toBitVec_retainedBits (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    BitVector.toBitVec retainedWidth
        (retainedBits retainedWidth discardedWidth value) =
      (BitVector.toBitVec (discardedWidth + retainedWidth) value).extractLsb'
        discardedWidth retainedWidth := by
  apply BitVec.eq_of_getElem_eq
  intro index inBounds
  calc
    (BitVector.toBitVec retainedWidth
        (retainedBits retainedWidth discardedWidth value))[index] =
        retainedBits retainedWidth discardedWidth value
          ⟨index, inBounds⟩ :=
      BitVector.getLsb_toBitVec retainedWidth
        (retainedBits retainedWidth discardedWidth value) ⟨index, inBounds⟩
    _ = value ⟨discardedWidth + index, by omega⟩ :=
      retainedBits_apply retainedWidth discardedWidth value ⟨index, inBounds⟩
    _ = (BitVector.toBitVec (discardedWidth + retainedWidth) value).getLsbD
        (discardedWidth + index) := by
      rw [BitVec.getLsbD_eq_getElem (by omega)]
      exact (BitVector.getLsb_toBitVec
        (discardedWidth + retainedWidth) value
        ⟨discardedWidth + index, by omega⟩).symm
    _ = ((BitVector.toBitVec (discardedWidth + retainedWidth) value).extractLsb'
        discardedWidth retainedWidth)[index] :=
      (BitVec.getElem_extractLsb' inBounds).symm

theorem extractLsb'_eq_extractLsb'_sshiftRight
    (retainedWidth discardedWidth : Nat)
    (value : BitVec (discardedWidth + retainedWidth)) :
    value.extractLsb' discardedWidth retainedWidth =
      (value.sshiftRight discardedWidth).extractLsb' 0 retainedWidth := by
  apply BitVec.eq_of_getElem_eq
  intro index inBounds
  rw [BitVec.getElem_extractLsb' inBounds,
    BitVec.getElem_extractLsb' inBounds]
  rw [BitVec.getLsbD_eq_getElem (by omega)]
  rw [BitVec.getLsbD_sshiftRight]
  have indexWithin : index < discardedWidth + retainedWidth := by omega
  have sourceWithin : discardedWidth + index <
      discardedWidth + retainedWidth := by omega
  simp [indexWithin, sourceWithin]

private theorem setWidth_ofInt_of_le {wide narrow : Nat}
    (widths : narrow ≤ wide) (value : Int) :
    (BitVec.ofInt wide value).setWidth narrow = BitVec.ofInt narrow value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have divisor : (2 ^ narrow : Int) ∣ (2 ^ wide : Int) :=
    pow_dvd_pow 2 widths
  have nested := Int.emod_emod_of_dvd value divisor
  have wideNonnegative : 0 ≤ value % (2 ^ wide : Nat) :=
    Int.emod_nonneg _ (by positivity)
  have lhsConversion :
      (value % (2 ^ wide : Nat)).toNat % 2 ^ narrow =
        ((value % (2 ^ wide : Nat)) % (2 ^ narrow : Nat)).toNat := by
    symm
    have powerToNat : ((2 : Int) ^ narrow).toNat = 2 ^ narrow := by
      simpa using Int.toNat_pow_of_nonneg (x := (2 : Int)) (by omega) narrow
    simpa [powerToNat] using Int.toNat_emod wideNonnegative
      (show 0 ≤ (2 ^ narrow : Int) by positivity)
  have nested' :
      value % ((2 ^ wide : Nat) : Int) % ((2 ^ narrow : Nat) : Int) =
        value % ((2 ^ narrow : Nat) : Int) := by
    simpa using nested
  rw [lhsConversion, nested']

private theorem getLsb_ofInt_eq_false_iff (width : Nat) (value : Int) :
    (BitVec.ofInt (width + 1) value).getLsb 0 = false ↔ value % 2 = 0 := by
  change (BitVec.ofInt (width + 1) value).toNat.testBit 0 = false ↔ _
  rw [← Nat.mod_two_eq_zero_iff_testBit_zero]
  rw [BitVec.toNat_ofInt]
  have divisor : (2 : Int) ∣ (2 ^ (width + 1) : Int) := by
    rw [pow_succ]
    exact ⟨2 ^ width, by ring⟩
  have nested := Int.emod_emod_of_dvd value divisor
  have wideNonnegative : 0 ≤ value % (2 ^ (width + 1) : Nat) :=
    Int.emod_nonneg _ (by positivity)
  have lhsConversion :
      (value % (2 ^ (width + 1) : Nat)).toNat % 2 =
        ((value % (2 ^ (width + 1) : Nat)) % 2).toNat := by
    symm
    simpa using Int.toNat_emod wideNonnegative
      (show 0 ≤ (2 : Int) by omega)
  rw [lhsConversion]
  have nested' :
      value % ((2 ^ (width + 1) : Nat) : Int) % 2 = value % 2 := by
    convert nested using 1
    norm_cast
  rw [nested']
  constructor
  · intro naturalZero
    have remainderNonnegative : 0 ≤ value % 2 :=
      Int.emod_nonneg _ (by omega)
    have remainderNonpositive := Int.toNat_eq_zero.mp naturalZero
    omega
  · intro remainderZero
    simp [remainderZero]

theorem discardedNat_eq_remainder (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    BitVector.toNat discardedWidth
        (discardedBits retainedWidth discardedWidth value) =
      ((BitVector.toBitVec (discardedWidth + retainedWidth) value).toInt %
        (2 ^ discardedWidth : Nat)).toNat := by
  let packed := BitVector.toBitVec (discardedWidth + retainedWidth) value
  have nativeEquation :
      BitVector.toBitVec discardedWidth
          (discardedBits retainedWidth discardedWidth value) =
        BitVec.ofInt discardedWidth packed.toInt := by
    calc
      BitVector.toBitVec discardedWidth
          (discardedBits retainedWidth discardedWidth value) =
          packed.extractLsb' 0 discardedWidth :=
        toBitVec_discardedBits retainedWidth discardedWidth value
      _ = packed.setWidth discardedWidth :=
        (BitVec.setWidth_eq_extractLsb' (by omega)).symm
      _ = (BitVec.ofInt (discardedWidth + retainedWidth) packed.toInt).setWidth
          discardedWidth := by rw [BitVec.ofInt_toInt]
      _ = BitVec.ofInt discardedWidth packed.toInt :=
        setWidth_ofInt_of_le (by omega) _
  have naturals := congrArg BitVec.toNat nativeEquation
  simpa [packed] using naturals

theorem toBitVec_retainedBits_eq_floor (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    BitVector.toBitVec retainedWidth
        (retainedBits retainedWidth discardedWidth value) =
      BitVec.ofInt retainedWidth
        ((BitVector.toBitVec (discardedWidth + retainedWidth) value).toInt /
          (2 ^ discardedWidth : Nat)) := by
  rw [toBitVec_retainedBits,
    extractLsb'_eq_extractLsb'_sshiftRight]
  rw [← BitVec.setWidth_eq_extractLsb' (show retainedWidth ≤
    discardedWidth + retainedWidth by omega)]
  rw [show (BitVector.toBitVec (discardedWidth + retainedWidth) value).sshiftRight
      discardedWidth =
      BitVec.ofInt (discardedWidth + retainedWidth)
        ((BitVector.toBitVec (discardedWidth + retainedWidth) value).toInt /
          (2 ^ discardedWidth : Nat)) by
    simp [BitVec.sshiftRight, Int.shiftRight_eq_div_pow]]
  exact setWidth_ofInt_of_le (by omega) _

@[simp] theorem guardBit_zero (retainedWidth : Nat)
    (value : Fin (0 + retainedWidth) → Bool) :
    guardBit retainedWidth 0 value = false := by
  simp [guardBit, guardLayout, VectorLayout.apply]

@[simp] theorem guardBit_succ (retainedWidth discardedWidth : Nat)
    (value : Fin ((discardedWidth + 1) + retainedWidth) → Bool) :
    guardBit retainedWidth (discardedWidth + 1) value =
      value ⟨discardedWidth, by omega⟩ := by
  simp [guardBit, guardLayout, VectorLayout.apply]

@[simp] theorem stickyBit_zero (retainedWidth : Nat)
    (value : Fin (0 + retainedWidth) → Bool) :
    stickyBit retainedWidth 0 value = false := by
  simp [stickyBit]

@[simp] theorem retainedLsbBit_zero (discardedWidth : Nat)
    (value : Fin discardedWidth → Bool) :
    retainedLsbBit 0 discardedWidth value = false := by
  simp [retainedLsbBit, retainedLsbLayout, VectorLayout.apply]

@[simp] theorem retainedLsbBit_succ (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + (retainedWidth + 1)) → Bool) :
    retainedLsbBit (retainedWidth + 1) discardedWidth value =
      value ⟨discardedWidth, by omega⟩ := by
  simp [retainedLsbBit, retainedLsbLayout, VectorLayout.apply]

theorem retainedLsbBit_succ_eq_false_iff (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + (retainedWidth + 1)) → Bool) :
    retainedLsbBit (retainedWidth + 1) discardedWidth value = false ↔
      ((BitVector.toBitVec (discardedWidth + (retainedWidth + 1)) value).toInt /
        (2 ^ discardedWidth : Nat)) % 2 = 0 := by
  let quotient :=
    (BitVector.toBitVec (discardedWidth + (retainedWidth + 1)) value).toInt /
      (2 ^ discardedWidth : Nat)
  have packedEquation :=
    toBitVec_retainedBits_eq_floor (retainedWidth + 1) discardedWidth value
  have lsbEquation :
      retainedBits (retainedWidth + 1) discardedWidth value 0 =
        (BitVec.ofInt (retainedWidth + 1) quotient).getLsb 0 := by
    simpa only [BitVector.getLsb_toBitVec] using
      congrArg (fun bits : BitVec (retainedWidth + 1) => bits.getLsb 0)
        packedEquation
  rw [retainedLsbBit_succ]
  change value ⟨discardedWidth, by omega⟩ = false ↔ quotient % 2 = 0
  have valueEquation :
      value ⟨discardedWidth, by omega⟩ =
        (BitVec.ofInt (retainedWidth + 1) quotient).getLsb 0 := by
    calc
      value ⟨discardedWidth, by omega⟩ =
          retainedBits (retainedWidth + 1) discardedWidth value 0 := by
        symm
        exact retainedBits_apply _ _ _ _
      _ = (BitVec.ofInt (retainedWidth + 1) quotient).getLsb 0 :=
        lsbEquation
  rw [valueEquation]
  exact getLsb_ofInt_eq_false_iff retainedWidth quotient

theorem stickyBit_succ (retainedWidth discardedWidth : Nat)
    (value : Fin ((discardedWidth + 1) + retainedWidth) → Bool) :
    stickyBit retainedWidth (discardedWidth + 1) value =
      Any.some discardedWidth fun index =>
        value ⟨index.val, by omega⟩ := by
  unfold stickyBit
  have layoutEquation :
      VectorLayout.apply
          (stickyLayout retainedWidth (discardedWidth + 1)) value =
        fun index =>
          if index.val + 1 < discardedWidth + 1 then
            value ⟨index.val, by omega⟩
          else false := by
    funext index
    by_cases belowGuard : index.val < discardedWidth
    · have condition : index.val + 1 < discardedWidth + 1 := by omega
      simp [VectorLayout.apply, stickyLayout, condition]
    · have condition : ¬index.val + 1 < discardedWidth + 1 := by omega
      simp [VectorLayout.apply, stickyLayout, condition]
  rw [layoutEquation]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro someTrue
    rcases (Any.some_eq_true_iff _ _).mp someTrue with ⟨index, indexTrue⟩
    have belowGuard : index.val < discardedWidth := by
      by_contra notBelow
      have condition : ¬index.val + 1 < discardedWidth + 1 := by omega
      simp [condition] at indexTrue
    apply (Any.some_eq_true_iff _ _).mpr
    exact ⟨⟨index.val, belowGuard⟩, by
      simpa [belowGuard] using indexTrue⟩
  · intro someTrue
    rcases (Any.some_eq_true_iff _ _).mp someTrue with ⟨index, indexTrue⟩
    apply (Any.some_eq_true_iff _ _).mpr
    exact ⟨index.castSucc, by simpa [index.isLt] using indexTrue⟩

theorem stickyBit_succ_eq_false_iff (retainedWidth discardedWidth : Nat)
    (value : Fin ((discardedWidth + 1) + retainedWidth) → Bool) :
    stickyBit retainedWidth (discardedWidth + 1) value = false ↔
      BitVector.toNat discardedWidth
        (fun index => value ⟨index.val, by omega⟩) = 0 := by
  rw [stickyBit_succ, Any.some_eq_false_iff,
    BitVector.toNat_eq_zero_iff]

theorem remainder_toNat_succ (retainedWidth discardedWidth : Nat)
    (value : Fin ((discardedWidth + 1) + retainedWidth) → Bool) :
    ((BitVector.toBitVec ((discardedWidth + 1) + retainedWidth) value).toInt %
        (2 ^ (discardedWidth + 1) : Nat)).toNat =
      (guardBit retainedWidth (discardedWidth + 1) value).toNat *
          2 ^ discardedWidth +
        BitVector.toNat discardedWidth
          (fun index => value ⟨index.val, by omega⟩) := by
  rw [← discardedNat_eq_remainder retainedWidth (discardedWidth + 1) value]
  cases selected : value ⟨discardedWidth, by omega⟩ <;>
    simp [BitVector.toNat, discardedBits, guardBit_succ,
      BitVector.cardinality_eq_pow, selected]

theorem toBitVec_circuitResult (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    BitVector.toBitVec retainedWidth
        (circuitResult retainedWidth discardedWidth value) =
      BitVec.ofInt retainedWidth
        ((BitVector.toBitVec (discardedWidth + retainedWidth) value).toInt /
            (2 ^ discardedWidth : Nat) +
          (roundUp retainedWidth discardedWidth value).toNat) := by
  cases rounds : roundUp retainedWidth discardedWidth value
  · simp [circuitResult, rounds, toBitVec_retainedBits_eq_floor]
  · simp only [circuitResult, rounds, Bool.toNat_true,
      Bool.cond_true]
    rw [toBitVec_incrementValue, toBitVec_retainedBits_eq_floor,
      BitVec.ofInt_add]
    simp

theorem roundNearestEven_eq_floor_add_roundUp
    (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + (retainedWidth + 1)) → Bool) :
    roundNearestEven discardedWidth
        (BitVector.toBitVec
          (discardedWidth + (retainedWidth + 1)) value).toInt =
      (BitVector.toBitVec
          (discardedWidth + (retainedWidth + 1)) value).toInt /
          (2 ^ discardedWidth : Nat) +
        (roundUp (retainedWidth + 1) discardedWidth value).toNat := by
  cases discardedWidth with
  | zero =>
      simp [roundNearestEven, roundUp]
  | succ discardedWidth =>
      let packed := BitVector.toBitVec
        ((discardedWidth + 1) + (retainedWidth + 1)) value
      let quotient := packed.toInt / (2 ^ (discardedWidth + 1) : Nat)
      let remainder := packed.toInt % (2 ^ (discardedWidth + 1) : Nat)
      let tail := BitVector.toNat discardedWidth
        (fun index => value ⟨index.val, by omega⟩)
      let guard :=
        guardBit (retainedWidth + 1) (discardedWidth + 1) value
      let sticky :=
        stickyBit (retainedWidth + 1) (discardedWidth + 1) value
      let parity :=
        retainedLsbBit (retainedWidth + 1) (discardedWidth + 1) value
      have remainderNonnegative : 0 ≤ remainder :=
        Int.emod_nonneg _ (by positivity)
      have remainderDecompositionNat :=
        remainder_toNat_succ (retainedWidth + 1) discardedWidth value
      have remainderDecomposition :
          remainder = guard.toNat * (2 ^ discardedWidth : Nat) + tail := by
        calc
          remainder = (remainder.toNat : Int) :=
            (Int.toNat_of_nonneg remainderNonnegative).symm
          _ = (guard.toNat * 2 ^ discardedWidth + tail : Nat) := by
            exact_mod_cast (show remainder.toNat =
              guard.toNat * 2 ^ discardedWidth + tail by
                simpa [remainder, packed, guard, tail] using
                  remainderDecompositionNat)
      have tailBound : tail < 2 ^ discardedWidth := by
        simpa [tail, BitVector.cardinality_eq_pow] using
          BitVector.toNat_lt_cardinality discardedWidth
            (fun index => value ⟨index.val, by omega⟩)
      have stickyZero : sticky = false ↔ tail = 0 := by
        simpa [sticky, tail] using
          stickyBit_succ_eq_false_iff
            (retainedWidth + 1) discardedWidth value
      have parityZero : parity = false ↔ quotient % 2 = 0 := by
        simpa [parity, quotient, packed] using
          retainedLsbBit_succ_eq_false_iff retainedWidth
            (discardedWidth + 1) value
      have roundUpEquation :
          roundUp (retainedWidth + 1) (discardedWidth + 1) value =
            (guard && (sticky || parity)) := rfl
      simp only [roundNearestEven]
      change (if 2 * remainder < (2 ^ (discardedWidth + 1) : Nat) then
          quotient
        else if (2 ^ (discardedWidth + 1) : Nat) < 2 * remainder then
          quotient + 1
        else if quotient % 2 = 0 then quotient else quotient + 1) =
        quotient +
          (roundUp (retainedWidth + 1) (discardedWidth + 1) value).toNat
      rw [roundUpEquation]
      have halfPositive : 0 < (2 ^ discardedWidth : Int) := by positivity
      have tailBoundInt : (tail : Int) < (2 ^ discardedWidth : Int) := by
        exact_mod_cast tailBound
      have divisorEquation :
          (2 ^ (discardedWidth + 1) : Int) =
            2 * (2 ^ discardedWidth : Int) := by
        simp [pow_succ, mul_comm]
      cases guardEquation : guard <;>
        cases stickyEquation : sticky <;>
        cases parityEquation : parity <;>
        simp [guardEquation] at remainderDecomposition <;>
        simp [stickyEquation] at stickyZero <;>
        simp [parityEquation] at parityZero <;>
        simp [divisorEquation] <;>
        omega

theorem circuitResult_eq_resultValue (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    circuitResult retainedWidth discardedWidth value =
      resultValue retainedWidth discardedWidth value := by
  unfold resultValue
  rw [← BitVector.ofBitVec_toBitVec retainedWidth
    (circuitResult retainedWidth discardedWidth value)]
  apply congrArg BitVector.ofBitVec
  cases retainedWidth with
  | zero =>
      exact Subsingleton.elim _ _
  | succ retainedWidth =>
      rw [toBitVec_circuitResult,
        ← roundNearestEven_eq_floor_add_roundUp]

end Silean.Modules.SignedRoundShift.Internal
