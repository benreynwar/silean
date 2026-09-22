import HTFFT.Fixed.Error

namespace HTFFT.Fixed

open HTFFT
open HTFFT.FixedPoint

/-- Rational approximations used to generate a stored twiddle table.  This is
executable data, not the mathematical specification of a root of unity. -/
structure RationalTwiddleTable (depth : Nat) where
  value : (stage : Fin depth) →
    Fin (2 ^ stage.val) → HTFFT.Complex Rat

/-- Quantize rational twiddle approximations using explicitly selected formats
and rounding policies.  Width is not applied here: representability remains a
separate proposition, just as it is for the rest of the pure fixed-point
model. -/
def quantizeTwiddleTable (formats : Fin depth → Format)
    (rounding : Fin depth → RoundingMode)
    (approximations : RationalTwiddleTable depth) : TwiddleTable depth where
  value stage offset :=
    FixedPoint.encodeComplex (rounding stage) (formats stage)
      (approximations.value stage offset)

@[simp]
theorem quantizeTwiddleTable_value (formats : Fin depth → Format)
    (rounding : Fin depth → RoundingMode)
    (approximations : RationalTwiddleTable depth) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    (quantizeTwiddleTable formats rounding approximations).value stage offset =
      FixedPoint.encodeComplex (rounding stage) (formats stage)
        (approximations.value stage offset) :=
  rfl

theorem exactTwiddle_of_offset_val_zero (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) (offsetZero : offset.val = 0) :
    exactTwiddle stage offset = 1 := by
  rw [exactTwiddle]
  have indexZero : Exact.halfIndexEquiv stage.val (Sum.inl offset) = 0 := by
    ext
    simpa using offsetZero
  rw [indexZero, Exact.twiddle_zero]

/-- A kernel-checked componentwise enclosure of the exact roots of unity by a
rational approximation table.  Each exact real and imaginary component lies
within `error stage` of the corresponding rational center.

The data may be produced by Lean or by an external interval generator; only a
proof of this proposition promotes it to a trusted numerical certificate. -/
structure TwiddleEnclosure (approximations : RationalTwiddleTable depth)
    (error : Fin depth → ℝ) : Prop where
  error_nonnegative : ∀ stage, 0 ≤ error stage
  real_lower : ∀ stage offset,
    (approximations.value stage offset).real - error stage ≤
      (exactTwiddle stage offset).re
  real_upper : ∀ stage offset,
    (exactTwiddle stage offset).re ≤
      (approximations.value stage offset).real + error stage
  imag_lower : ∀ stage offset,
    (approximations.value stage offset).imag - error stage ≤
      (exactTwiddle stage offset).im
  imag_upper : ∀ stage offset,
    (exactTwiddle stage offset).im ≤
      (approximations.value stage offset).imag + error stage

/-- The direct componentwise consequence of a rectangular enclosure. -/
theorem TwiddleEnclosure.componentWithin
    {approximations : RationalTwiddleTable depth}
    {error : Fin depth → ℝ}
    (enclosure : TwiddleEnclosure approximations error)
    (stage : Fin depth) (offset : Fin (2 ^ stage.val)) :
    componentNorm
        (rationalComplexToComplex (approximations.value stage offset) -
          exactTwiddle stage offset) ≤
      error stage := by
  apply max_le
  · rw [Complex.sub_re, rationalComplexToComplex_re, abs_le]
    constructor
    · linarith [enclosure.real_upper stage offset]
    · linarith [enclosure.real_lower stage offset]
  · rw [Complex.sub_im, rationalComplexToComplex_im, abs_le]
    constructor
    · linarith [enclosure.imag_upper stage offset]
    · linarith [enclosure.imag_lower stage offset]

/-- Convert a rectangular component enclosure to Euclidean complex error. -/
theorem TwiddleEnclosure.normWithin
    {approximations : RationalTwiddleTable depth}
    {error : Fin depth → ℝ}
    (enclosure : TwiddleEnclosure approximations error)
    (stage : Fin depth) (offset : Fin (2 ^ stage.val)) :
    ‖rationalComplexToComplex (approximations.value stage offset) -
        exactTwiddle stage offset‖ ≤
      Real.sqrt 2 * error stage := by
  exact (norm_le_sqrtTwo_mul_componentNorm _).trans
    (mul_le_mul_of_nonneg_left (enclosure.componentWithin stage offset)
      (Real.sqrt_nonneg _))

/-- The generated integer table fits the selected twiddle formats. -/
def QuantizedTwiddleFits (formats : Fin depth → Format)
    (rounding : Fin depth → RoundingMode)
    (approximations : RationalTwiddleTable depth) : Prop :=
  ∀ stage offset,
    ComplexFits (formats stage)
      ((quantizeTwiddleTable formats rounding approximations).value
        stage offset)

/-- Quantizing a certified rectangular enclosure produces a Euclidean
`TwiddleAccuracy` certificate. Both componentwise terms acquire the exact
conversion factor `sqrt 2`. -/
theorem twiddleAccuracy_of_enclosure (config : Config depth)
    (rounding : Fin depth → RoundingMode)
    (approximations : RationalTwiddleTable depth)
    (approximationError : Fin depth → ℝ)
    (enclosure : TwiddleEnclosure approximations approximationError)
    (fits : QuantizedTwiddleFits config.twiddleFormat rounding approximations) :
    TwiddleAccuracy config
      (quantizeTwiddleTable config.twiddleFormat rounding approximations)
      (fun stage => Real.sqrt 2 *
        (approximationError stage + quantum (config.twiddleFormat stage))) := by
  refine
    { error_nonnegative := fun stage => mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg (enclosure.error_nonnegative stage)
          (quantum_nonnegative (config.twiddleFormat stage)))
      fits := fits
      accurate := ?_ }
  intro stage offset
  calc
    ‖decodeTwiddle config
            (quantizeTwiddleTable config.twiddleFormat rounding approximations)
            stage offset - exactTwiddle stage offset‖ ≤
        ‖decodeTwiddle config
                (quantizeTwiddleTable config.twiddleFormat rounding approximations)
                stage offset -
              rationalComplexToComplex
                (approximations.value stage offset)‖ +
          ‖rationalComplexToComplex
                (approximations.value stage offset) -
              exactTwiddle stage offset‖ := norm_sub_triangle _ _ _
    _ ≤ Real.sqrt 2 * quantum (config.twiddleFormat stage) +
        Real.sqrt 2 * approximationError stage := by
      apply add_le_add
      · simpa [decodeTwiddle] using
          (encodeComplex_error (rounding stage)
            (config.twiddleFormat stage)
            (approximations.value stage offset))
      · exact enclosure.normWithin stage offset
    _ = Real.sqrt 2 *
        (approximationError stage + quantum (config.twiddleFormat stage)) := by
      ring

end HTFFT.Fixed
