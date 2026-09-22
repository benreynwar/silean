import HTFFT.FixedPoint
import Mathlib.Tactic

namespace HTFFT.FixedPoint

/-- For a positive denominator, every supported rounding mode chooses either
the Euclidean quotient or the next integer.  This common characterization is
enough for the conservative one-LSB error theorem below. -/
theorem roundRatio_eq_ediv_or_succ (mode : RoundingMode) (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    roundRatio mode numerator denominator =
        numerator / (denominator : Int) ∨
      roundRatio mode numerator denominator =
        numerator / (denominator : Int) + 1 := by
  have denominatorNonzero : denominator ≠ 0 := Nat.ne_of_gt positive
  unfold roundRatio
  simp only [denominatorNonzero, ↓reduceIte]
  cases mode with
  | towardNegative => exact Or.inl rfl
  | towardZero =>
      change numerator.tdiv (denominator : Int) =
          numerator / (denominator : Int) ∨
        numerator.tdiv (denominator : Int) =
          numerator / (denominator : Int) + 1
      have denominatorSign : (denominator : Int).sign = 1 := by
        rw [Int.sign_eq_one_iff_pos]
        omega
      have divisionRelation :=
        (Int.ediv_eq_tdiv (a := numerator) (b := (denominator : Int)))
      rw [denominatorSign] at divisionRelation
      by_cases same : 0 ≤ numerator ∨ (denominator : Int) ∣ numerator
      · left
        rw [divisionRelation, if_pos same, sub_zero]
      · right
        rw [divisionRelation, if_neg same]
        omega
  | nearestTiesToEven =>
      dsimp only
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact Or.inr rfl

/-- Multiplying a rounded quotient back by its positive denominator differs
from the original numerator by at most that denominator. -/
theorem roundRatio_residual_le (mode : RoundingMode) (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    |roundRatio mode numerator denominator * (denominator : Int) - numerator| ≤
      (denominator : Int) := by
  have denominatorIntPositive : 0 < (denominator : Int) := by omega
  have denominatorIntNonzero : (denominator : Int) ≠ 0 :=
    ne_of_gt denominatorIntPositive
  have remainderNonnegative :
      0 ≤ numerator % (denominator : Int) :=
    Int.emod_nonneg _ denominatorIntNonzero
  have remainderLess :
      numerator % (denominator : Int) < (denominator : Int) :=
    Int.emod_lt_of_pos _ denominatorIntPositive
  have decomposition := Int.ediv_mul_add_emod numerator (denominator : Int)
  rcases roundRatio_eq_ediv_or_succ mode numerator denominator positive with
    quotient | successor
  · rw [quotient, abs_le]
    constructor <;> omega
  · have successorProduct :
        (numerator / (denominator : Int) + 1) * (denominator : Int) =
          numerator / (denominator : Int) * (denominator : Int) +
            (denominator : Int) := by ring
    rw [successor, successorProduct, abs_le]
    constructor <;> omega

/-- A rounded quotient differs from the exact rational quotient by at most
one integer unit. -/
theorem roundRatio_error_le_one (mode : RoundingMode) (numerator : Int)
    (denominator : Nat) (positive : 0 < denominator) :
    |(roundRatio mode numerator denominator : Rat) -
        Rat.divInt numerator denominator| ≤ 1 := by
  have residual := roundRatio_residual_le mode numerator denominator positive
  have denominatorPositive : (0 : Rat) < denominator := by
    positivity
  rw [Rat.divInt_eq_div, abs_le]
  constructor
  · rw [← mul_le_mul_iff_of_pos_right denominatorPositive]
    field_simp
    exact_mod_cast (abs_le.mp residual).1
  · rw [← mul_le_mul_iff_of_pos_right denominatorPositive]
    field_simp
    exact_mod_cast (abs_le.mp residual).2

theorem Format.scale_pos (format : Format) : 0 < format.scale := by
  simp [Format.scale]

theorem Format.scale_ne_zero (format : Format) : format.scale ≠ 0 :=
  Nat.ne_of_gt format.scale_pos

theorem scale_mul_pow_sub_of_le (source destination : Format)
    (ordered : source.fractionalBits ≤ destination.fractionalBits) :
    source.scale *
        2 ^ (destination.fractionalBits - source.fractionalBits) =
      destination.scale := by
  rw [Format.scale, Format.scale, ← Nat.pow_add]
  congr
  omega

theorem scale_mul_pow_sub_of_ge (source destination : Format)
    (ordered : destination.fractionalBits ≤ source.fractionalBits) :
    destination.scale *
        2 ^ (source.fractionalBits - destination.fractionalBits) =
      source.scale := by
  rw [Format.scale, Format.scale, ← Nat.pow_add]
  congr
  omega

/-- Increasing the number of fractional bits is exact: it appends zero low
bits and does not change the represented rational value. -/
theorem decode_rescale_of_le (mode : RoundingMode) (source destination : Format)
    (raw : Int)
    (ordered : source.fractionalBits ≤ destination.fractionalBits) :
    decode destination
        (rescale mode source.fractionalBits destination.fractionalBits raw) =
      decode source raw := by
  rw [rescale, if_pos ordered, decode, decode, Rat.divInt_eq_div,
    Rat.divInt_eq_div]
  have scaleFactor := scale_mul_pow_sub_of_le source destination ordered
  have sourceScaleNonzero : (source.scale : Rat) ≠ 0 := by
    exact_mod_cast source.scale_ne_zero
  have destinationScaleNonzero : (destination.scale : Rat) ≠ 0 := by
    exact_mod_cast destination.scale_ne_zero
  have scaleFactorRat :
      (source.scale : Rat) *
          (2 ^ (destination.fractionalBits - source.fractionalBits) : Nat) =
        (destination.scale : Rat) := by
    exact_mod_cast scaleFactor
  push_cast at scaleFactorRat
  push_cast
  field_simp
  calc
    (raw : Rat) *
          (2 : Rat) ^ (destination.fractionalBits - source.fractionalBits) *
        source.scale =
      raw * (source.scale *
        (2 : Rat) ^ (destination.fractionalBits - source.fractionalBits)) := by
        ring
    _ = raw * destination.scale := by rw [scaleFactorRat]

/-- Rescaling changes the decoded value by at most one destination LSB.  The
bound is zero when fractional precision grows, and conservative for all three
rounding modes when precision is discarded. -/
theorem decode_rescale_error (mode : RoundingMode) (source destination : Format)
    (raw : Int) :
    |decode destination
          (rescale mode source.fractionalBits destination.fractionalBits raw) -
        decode source raw| ≤ destination.quantum := by
  by_cases ordered : source.fractionalBits ≤ destination.fractionalBits
  · rw [decode_rescale_of_le mode source destination raw ordered]
    simp [Format.quantum, Rat.divInt_eq_div]
  · have reverseOrdered :
        destination.fractionalBits ≤ source.fractionalBits := by omega
    have gapPositive :
        0 < 2 ^ (source.fractionalBits - destination.fractionalBits) := by
      positivity
    have rounded := roundRatio_error_le_one mode raw
      (2 ^ (source.fractionalBits - destination.fractionalBits)) gapPositive
    have scaleFactor :=
      scale_mul_pow_sub_of_ge source destination reverseOrdered
    have identity :
        decode destination
            (roundRatio mode raw
              (2 ^ (source.fractionalBits - destination.fractionalBits))) -
          decode source raw =
        ((roundRatio mode raw
              (2 ^ (source.fractionalBits - destination.fractionalBits)) : Rat) -
            Rat.divInt raw
              (2 ^ (source.fractionalBits - destination.fractionalBits))) /
          destination.scale := by
      rw [decode, decode, Rat.divInt_eq_div, Rat.divInt_eq_div,
        Rat.divInt_eq_div]
      have sourceScaleNonzero : (source.scale : Rat) ≠ 0 := by
        exact_mod_cast source.scale_ne_zero
      have destinationScaleNonzero : (destination.scale : Rat) ≠ 0 := by
        exact_mod_cast destination.scale_ne_zero
      have gapNonzero :
          ((2 ^ (source.fractionalBits - destination.fractionalBits) : Nat) :
            Rat) ≠ 0 := by positivity
      have scaleFactorRat :
          (destination.scale : Rat) *
              (2 ^ (source.fractionalBits - destination.fractionalBits) : Nat) =
            (source.scale : Rat) := by
        exact_mod_cast scaleFactor
      push_cast at scaleFactorRat
      push_cast
      field_simp
      rw [← scaleFactorRat]
      ring
    rw [rescale, if_neg ordered, identity, abs_div]
    rw [Format.quantum, Rat.divInt_eq_div]
    have destinationScalePositive : (0 : Rat) < destination.scale := by
      exact_mod_cast destination.scale_pos
    rw [abs_of_nonneg destinationScalePositive.le]
    simpa [Rat.divInt_eq_div] using
      (div_le_div_of_nonneg_right rounded destinationScalePositive.le)

/-- Quantizing and decoding a rational changes it by at most one destination
LSB. -/
theorem decode_encode_error (mode : RoundingMode) (format : Format)
    (value : Rat) :
    |decode format (encode mode format value) - value| ≤ format.quantum := by
  have rounded := roundRatio_error_le_one mode (value.num * format.scale)
    value.den value.den_pos
  have quotientIdentity :
      Rat.divInt (value.num * format.scale) value.den =
        value * format.scale := by
    calc
      Rat.divInt (value.num * format.scale) value.den =
          Rat.divInt value.num value.den * format.scale := by
        rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
        push_cast
        ring
      _ = value * format.scale := by rw [value.num_divInt_den]
  rw [quotientIdentity] at rounded
  have scalePositive : (0 : Rat) < format.scale := by
    exact_mod_cast format.scale_pos
  have differenceIdentity :
      decode format (encode mode format value) - value =
        ((encode mode format value : Int) : Rat) / format.scale - value := by
    rw [decode, Rat.divInt_eq_div]
    push_cast
    rfl
  rw [differenceIdentity]
  have scaledDifference :
      ((encode mode format value : Int) : Rat) / format.scale - value =
        (((encode mode format value : Int) : Rat) -
          value * format.scale) / format.scale := by
    field_simp
  rw [scaledDifference, abs_div, abs_of_nonneg scalePositive.le,
    Format.quantum, Rat.divInt_eq_div]
  exact div_le_div_of_nonneg_right rounded scalePositive.le

/-- Two's-complement wrapping is the identity on the representable interval. -/
theorem wrapSigned_eq_of_fits {width : Nat} {raw : Int}
    (fits : FitsWidth width raw) :
    wrapSigned width raw = raw := by
  unfold wrapSigned
  apply Int.bmod_eq_of_le
  · cases width with
    | zero => simpa [FitsWidth, signedMin, signedMax] using fits.1
    | succ width =>
        simpa [FitsWidth, signedMin, signedMax, pow_succ] using fits.1
  · cases width with
    | zero =>
        have upper := fits.2
        simp [signedMax] at upper ⊢
        omega
    | succ width =>
        have upper := fits.2
        simp [signedMax, pow_succ] at upper ⊢
        omega

theorem wrapSigned_eq_of_format_fits {format : Format} {raw : Int}
    (fits : Fits format raw) :
    wrapSigned format.width raw = raw :=
  wrapSigned_eq_of_fits fits

@[simp]
theorem decode_zero (format : Format) : decode format 0 = 0 := by
  simp [decode, Rat.divInt_eq_div]

theorem decode_add (format : Format) (left right : Int) :
    decode format (left + right) =
      decode format left + decode format right := by
  rw [decode, decode, decode, Rat.divInt_eq_div, Rat.divInt_eq_div,
    Rat.divInt_eq_div]
  push_cast
  ring

theorem decode_sub (format : Format) (left right : Int) :
    decode format (left - right) =
      decode format left - decode format right := by
  rw [decode, decode, decode, Rat.divInt_eq_div, Rat.divInt_eq_div,
    Rat.divInt_eq_div]
  push_cast
  ring

/-- Multiplying raw integers adds their fractional-bit counts. -/
theorem decode_mul (leftFormat rightFormat : Format) (left right : Int) :
    decode ⟨0, leftFormat.fractionalBits + rightFormat.fractionalBits⟩
        (left * right) =
      decode leftFormat left * decode rightFormat right := by
  rw [decode, decode, decode, Rat.divInt_eq_div, Rat.divInt_eq_div,
    Rat.divInt_eq_div, Format.scale, Format.scale, Format.scale, Nat.pow_add]
  push_cast
  ring

theorem decodeComplex_add (format : Format)
    (left right : HTFFT.Complex Int) :
    decodeComplex format (left + right) =
      decodeComplex format left + decodeComplex format right := by
  rcases left with ⟨leftReal, leftImag⟩
  rcases right with ⟨rightReal, rightImag⟩
  change
    ({ real := decode format (leftReal + rightReal)
       imag := decode format (leftImag + rightImag) } : HTFFT.Complex Rat) =
    { real := decode format leftReal + decode format rightReal
      imag := decode format leftImag + decode format rightImag }
  rw [decode_add, decode_add]

theorem decodeComplex_sub (format : Format)
    (left right : HTFFT.Complex Int) :
    decodeComplex format (left - right) =
      decodeComplex format left - decodeComplex format right := by
  rcases left with ⟨leftReal, leftImag⟩
  rcases right with ⟨rightReal, rightImag⟩
  change
    ({ real := decode format (leftReal - rightReal)
       imag := decode format (leftImag - rightImag) } : HTFFT.Complex Rat) =
    { real := decode format leftReal - decode format rightReal
      imag := decode format leftImag - decode format rightImag }
  rw [decode_sub, decode_sub]

end HTFFT.FixedPoint
