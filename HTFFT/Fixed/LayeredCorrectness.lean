import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.Exact.LayeredCorrectness
import Mathlib.Tactic

namespace HTFFT.Fixed

theorem advanceBounds_nonnegative (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) (bounds : Bounds)
    (boundsNonnegative : bounds.Nonnegative)
    (twiddleNonnegative : 0 ≤ twiddleError stage) :
    (advanceBounds config twiddleError stage bounds).Nonnegative := by
  rcases boundsNonnegative with ⟨magnitudeNonnegative, errorNonnegative⟩
  constructor
  · simp [advanceBounds]
    positivity
  · simp only [advanceBounds]
    have coefficientNonnegative : 0 ≤ 2 + twiddleError stage := by
      positivity
    have firstTerm :
        0 ≤ (2 + twiddleError stage) * bounds.error :=
      mul_nonneg coefficientNonnegative errorNonnegative
    have secondTerm :
        0 ≤ bounds.magnitude * twiddleError stage := by
      positivity
    have arithmeticTerm :=
      arithmeticError_nonnegative (config.butterfly stage)
    linarith

theorem boundsAt_nonnegative (config : Config depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds)
    (initialNonnegative : initial.Nonnegative)
    (twiddleNonnegative : ∀ stage, 0 ≤ twiddleError stage)
    (boundary : Exact.LayerBoundary depth) :
    (boundsAt config twiddleError initial boundary).Nonnegative := by
  induction boundary using Fin.induction with
  | zero => simpa [boundsAt, Exact.butterflyStagePrefix,
      Exact.butterflyStages] using initialNonnegative
  | succ stage inductionHypothesis =>
      rw [boundsAt_boundarySucc]
      exact advanceBounds_nonnegative config twiddleError stage _
        inductionHypothesis (twiddleNonnegative stage)

/-- Exact closed form for the magnitude component of the recurrence. After
`s` layers it is `2^s` times the initial bound, matching the size scaling of
an unnormalized radix-two FFT. -/
theorem boundsAt_magnitude (config : Config depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds)
    (boundary : Exact.LayerBoundary depth) :
    (boundsAt config twiddleError initial boundary).magnitude =
      (2 : ℝ) ^ boundary.val * initial.magnitude := by
  induction boundary using Fin.induction with
  | zero =>
      simp [boundsAt, Exact.butterflyStagePrefix, Exact.butterflyStages]
  | succ stage inductionHypothesis =>
      rw [boundsAt_boundarySucc]
      simp only [advanceBounds, inductionHypothesis]
      change 2 * ((2 : ℝ) ^ stage.val * initial.magnitude) =
        (2 : ℝ) ^ (stage.val + 1) * initial.magnitude
      rw [pow_succ]
      ring

/-- In the baseline case of exact twiddles and a uniform local arithmetic
allowance `R`, the error recurrence has the closed form
`2^s * E₀ + (2^s - 1) * R`. Thus the generic propagation is linear in the
transform size `N = 2^s`, rather than `3^s`. -/
theorem boundsAt_error_of_exactTwiddles
    (config : Config depth) (twiddleError : Fin depth → ℝ)
    (initial : Bounds) (roundingError : ℝ)
    (twiddleExact : ∀ stage, twiddleError stage = 0)
    (arithmeticConstant : ∀ stage,
      arithmeticError (config.butterfly stage) = roundingError)
    (boundary : Exact.LayerBoundary depth) :
    (boundsAt config twiddleError initial boundary).error =
      (2 : ℝ) ^ boundary.val * initial.error +
        ((2 : ℝ) ^ boundary.val - 1) * roundingError := by
  induction boundary using Fin.induction with
  | zero =>
      simp [boundsAt, Exact.butterflyStagePrefix, Exact.butterflyStages]
  | succ stage inductionHypothesis =>
      rw [boundsAt_boundarySucc]
      simp only [advanceBounds, twiddleExact stage, arithmeticConstant stage,
        inductionHypothesis]
      change
        (2 + 0) *
              ((2 : ℝ) ^ stage.val * initial.error +
                ((2 : ℝ) ^ stage.val - 1) * roundingError) +
            (boundsAt config twiddleError initial stage.castSucc).magnitude * 0 +
          roundingError =
        (2 : ℝ) ^ (stage.val + 1) * initial.error +
          ((2 : ℝ) ^ (stage.val + 1) - 1) * roundingError
      rw [pow_succ]
      ring

/-- One exact FFT layer grows a uniform Euclidean magnitude bound by at most a
factor of two. -/
theorem butterflyLayer_magnitudeBound (stage : Fin depth)
    (input : Exact.Vector depth ℂ) {magnitude : ℝ}
    (inputBound : MagnitudeBound magnitude input) :
    MagnitudeBound (2 * magnitude)
      (Exact.butterflyLayer depth stage input) := by
  intro outputIndex
  obtain ⟨position, rfl⟩ :=
    (Exact.layerIndexEquiv depth stage).surjective outputIndex
  rcases position with ⟨group, branch, offset⟩
  by_cases branchZero : branch = 0
  · subst branch
    rw [Exact.butterflyLayer_first]
    apply norm_ideal_upper_le
    · exact inputBound _
    · exact inputBound _
    · exact norm_exactTwiddle stage offset
  · have branchOne : branch = 1 := by
      apply Fin.ext
      omega
    subst branch
    rw [Exact.butterflyLayer_second]
    apply norm_ideal_lower_le
    · exact inputBound _
    · exact inputBound _
    · exact norm_exactTwiddle stage offset

/-- One fixed layer advances the uniform error recurrence, assuming the exact
input magnitude bound, the previous decoded-data error bound, a certified
twiddle table, and absence of overflow in this layer. -/
theorem butterflyLayer_within (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (stage : Fin depth) (fixedInput : Vector depth)
    (exactInput : Exact.Vector depth ℂ) (bounds : Bounds)
    (magnitudeNonnegative : 0 ≤ bounds.magnitude)
    (errorNonnegative : 0 ≤ bounds.error)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound bounds.magnitude exactInput)
    (inputWithin : Within bounds.error
      (decodeVector config stage.castSucc fixedInput) exactInput)
    (noOverflow : LayerNoOverflow config table stage fixedInput) :
    Within (advanceBounds config twiddleError stage bounds).error
      (decodeVector config stage.succ
        (butterflyLayer config table stage fixedInput))
      (Exact.butterflyLayer depth stage exactInput) := by
  intro outputIndex
  obtain ⟨position, rfl⟩ :=
    (Exact.layerIndexEquiv depth stage).surjective outputIndex
  rcases position with ⟨group, branch, offset⟩
  have twiddleNonnegative := twiddleAccuracy.error_nonnegative stage
  have exactTwiddleBound := norm_exactTwiddle stage offset
  have firstClose := inputWithin
    (Exact.layerIndexEquiv depth stage
      { group := group, branch := 0, offset := offset })
  have secondClose := inputWithin
    (Exact.layerIndexEquiv depth stage
      { group := group, branch := 1, offset := offset })
  have secondMagnitude := inputMagnitude
    (Exact.layerIndexEquiv depth stage
      { group := group, branch := 1, offset := offset })
  have storedTwiddleClose := twiddleAccuracy.accurate stage offset
  have butterflyNoOverflow := noOverflow group offset
  by_cases branchZero : branch = 0
  · subst branch
    simp only [decodeVector]
    rw [butterflyLayer_first, Exact.butterflyLayer_first]
    have propagated := Butterfly.Fixed.butterfly_upper_error
      (config := config.butterfly stage)
      (exactA := exactInput (Exact.layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }))
      (exactB := exactInput (Exact.layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }))
      (exactTwiddle := exactTwiddle stage offset)
      magnitudeNonnegative errorNonnegative twiddleNonnegative
      secondMagnitude exactTwiddleBound
      (by simpa [decodeVector, Config.butterfly] using firstClose)
      (by simpa [decodeVector, Config.butterfly] using secondClose)
      (by simpa [decodeTwiddle, Config.butterfly] using storedTwiddleClose)
      butterflyNoOverflow
    simpa [decodeVector, advanceBounds, Config.butterfly, exactTwiddle] using
      propagated
  · have branchOne : branch = 1 := by
      apply Fin.ext
      omega
    subst branch
    simp only [decodeVector]
    rw [butterflyLayer_second, Exact.butterflyLayer_second]
    have propagated := Butterfly.Fixed.butterfly_lower_error
      (config := config.butterfly stage)
      (exactA := exactInput (Exact.layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }))
      (exactB := exactInput (Exact.layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }))
      (exactTwiddle := exactTwiddle stage offset)
      magnitudeNonnegative errorNonnegative twiddleNonnegative
      secondMagnitude exactTwiddleBound
      (by simpa [decodeVector, Config.butterfly] using firstClose)
      (by simpa [decodeVector, Config.butterfly] using secondClose)
      (by simpa [decodeTwiddle, Config.butterfly] using storedTwiddleClose)
      butterflyNoOverflow
    simpa [decodeVector, advanceBounds, Config.butterfly, exactTwiddle] using
      propagated

/-- A layer satisfying its concrete no-overflow predicate produces values
representable in the next boundary format. -/
theorem butterflyLayer_fits (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth)
    (noOverflow : LayerNoOverflow config table stage input) :
    VectorFits config stage.succ (butterflyLayer config table stage input) := by
  intro outputIndex
  obtain ⟨position, rfl⟩ :=
    (Exact.layerIndexEquiv depth stage).surjective outputIndex
  rcases position with ⟨group, branch, offset⟩
  have butterflyNoOverflow := noOverflow group offset
  by_cases branchZero : branch = 0
  · subst branch
    rw [butterflyLayer_first,
      Butterfly.Fixed.butterfly_eq_outputRounded_of_noOverflow
        butterflyNoOverflow]
    exact butterflyNoOverflow.2.2.2.2.2.1
  · have branchOne : branch = 1 := by
      apply Fin.ext
      omega
    subst branch
    rw [butterflyLayer_second,
      Butterfly.Fixed.butterfly_eq_outputRounded_of_noOverflow
        butterflyNoOverflow]
    exact butterflyNoOverflow.2.2.2.2.2.2

/-- Representability is preserved at every boundary of a no-overflow network. -/
theorem layeredPrefix_fits (config : Config depth)
    (table : TwiddleTable depth) (input : Vector depth)
    (inputFits : VectorFits config 0 input)
    (noOverflow : NoOverflow config table input)
    (boundary : Exact.LayerBoundary depth) :
    VectorFits config boundary (layeredPrefix config table boundary input) := by
  induction boundary using Fin.induction with
  | zero =>
      intro index
      simpa [layeredPrefix_zero, Exact.bitReverse] using
        inputFits (Exact.bitReverseIndex index)
  | succ stage inductionHypothesis =>
      rw [layeredPrefix_boundarySucc]
      exact butterflyLayer_fits config table stage _ (noOverflow stage)

theorem layeredFFT_fits (config : Config depth)
    (table : TwiddleTable depth) (input : Vector depth)
    (inputFits : VectorFits config 0 input)
    (noOverflow : NoOverflow config table input) :
    VectorFits config (Fin.last depth) (layeredFFT config table input) := by
  simpa only [layeredPrefix_final] using
    layeredPrefix_fits config table input inputFits noOverflow (Fin.last depth)

/-- Uniform magnitude and numerical-error invariants at every layer boundary. -/
theorem layeredPrefix_bounds (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (noOverflow : NoOverflow config table fixedInput)
    (boundary : Exact.LayerBoundary depth) :
    MagnitudeBound
        (boundsAt config twiddleError initial boundary).magnitude
        (Exact.layeredPrefix depth boundary exactInput) ∧
      Within (boundsAt config twiddleError initial boundary).error
        (decodeVector config boundary
          (layeredPrefix config table boundary fixedInput))
        (Exact.layeredPrefix depth boundary exactInput) := by
  induction boundary using Fin.induction with
  | zero =>
      constructor
      · intro index
        simpa [boundsAt, Exact.butterflyStagePrefix,
          Exact.butterflyStages, Exact.layeredPrefix_zero,
          MagnitudeBound, Exact.bitReverse] using
          inputMagnitude (Exact.bitReverseIndex index)
      · intro index
        simpa [boundsAt, Exact.butterflyStagePrefix,
          Exact.butterflyStages, layeredPrefix_zero,
          Exact.layeredPrefix_zero, decodeVector, Exact.bitReverse] using
          inputWithin (Exact.bitReverseIndex index)
  | succ stage inductionHypothesis =>
      have previousNonnegative := boundsAt_nonnegative config twiddleError
        initial initialNonnegative twiddleAccuracy.error_nonnegative stage.castSucc
      rw [boundsAt_boundarySucc, layeredPrefix_boundarySucc,
        Exact.layeredPrefix_boundarySucc]
      constructor
      · exact butterflyLayer_magnitudeBound stage _ inductionHypothesis.1
      · exact butterflyLayer_within config table twiddleError stage _ _ _
          previousNonnegative.1 previousNonnegative.2 twiddleAccuracy
          inductionHypothesis.1 inductionHypothesis.2 (noOverflow stage)

/-- Complete-network bound relative to an arbitrary mathematical input.  A
nonzero initial error captures input quantization explicitly. -/
theorem layeredFFT_within (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (noOverflow : NoOverflow config table fixedInput) :
    Within
      (boundsAt config twiddleError initial (Fin.last depth)).error
      (decodeVector config (Fin.last depth)
        (layeredFFT config table fixedInput))
      (Exact.layeredFFT depth exactInput) := by
  have result := (layeredPrefix_bounds config table twiddleError fixedInput
    exactInput initial initialNonnegative twiddleAccuracy inputMagnitude
    inputWithin noOverflow (Fin.last depth)).2
  simpa only [layeredPrefix_final, Exact.layeredPrefix_final] using result

/-- When the mathematical input is the value decoded from the actual input
bits, the initial numerical error is zero. -/
theorem layeredFFT_within_decodedInput (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (inputMagnitude : ℝ)
    (inputMagnitudeNonnegative : 0 ≤ inputMagnitude)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (decodedInputMagnitude : MagnitudeBound inputMagnitude
      (decodeVector config 0 fixedInput))
    (noOverflow : NoOverflow config table fixedInput) :
    Within
      (boundsAt config twiddleError
        { magnitude := inputMagnitude, error := 0 }
        (Fin.last depth)).error
      (decodeVector config (Fin.last depth)
        (layeredFFT config table fixedInput))
      (Exact.layeredFFT depth (decodeVector config 0 fixedInput)) := by
  apply layeredFFT_within config table twiddleError fixedInput
    (decodeVector config 0 fixedInput)
    { magnitude := inputMagnitude, error := 0 }
    ⟨inputMagnitudeNonnegative, le_refl 0⟩ twiddleAccuracy
    decodedInputMagnitude
  · intro index
    simp
  · exact noOverflow

/-- Explicit pre-quantization form: `inputError` bounds the discrepancy
between decoded input words and the intended mathematical input. -/
theorem layeredFFT_within_quantizedInput (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (inputMagnitude inputError : ℝ)
    (inputMagnitudeNonnegative : 0 ≤ inputMagnitude)
    (inputErrorNonnegative : 0 ≤ inputError)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (exactInputMagnitude : MagnitudeBound inputMagnitude exactInput)
    (inputQuantization : Within inputError
      (decodeVector config 0 fixedInput) exactInput)
    (noOverflow : NoOverflow config table fixedInput) :
    Within
      (boundsAt config twiddleError
        { magnitude := inputMagnitude, error := inputError }
        (Fin.last depth)).error
      (decodeVector config (Fin.last depth)
        (layeredFFT config table fixedInput))
      (Exact.layeredFFT depth exactInput) :=
  layeredFFT_within config table twiddleError fixedInput exactInput
    { magnitude := inputMagnitude, error := inputError }
    ⟨inputMagnitudeNonnegative, inputErrorNonnegative⟩ twiddleAccuracy
    exactInputMagnitude inputQuantization noOverflow

theorem encodeInput_within (config : Config depth)
    (rounding : FixedPoint.RoundingMode)
    (input : Fin (2 ^ depth) → HTFFT.Complex Rat) :
    Within (Real.sqrt 2 * quantum (config.boundaryFormat 0))
      (decodeVector config 0 (encodeInput config rounding input))
      (rationalInputToComplex input) := by
  intro index
  exact encodeComplex_error rounding (config.boundaryFormat 0) (input index)

/-- The componentwise quantization bound used only to certify fixed-width
range after input encoding. -/
theorem encodeInput_componentMagnitudeBound (config : Config depth)
    (rounding : FixedPoint.RoundingMode)
    (input : Fin (2 ^ depth) → HTFFT.Complex Rat) (magnitude : ℝ)
    (inputMagnitude : MagnitudeBound magnitude
      (rationalInputToComplex input)) :
    ComponentMagnitudeBound (magnitude + quantum (config.boundaryFormat 0))
      (decodeVector config 0 (encodeInput config rounding input)) := by
  intro index
  calc
    componentNorm
        (decodeVector config 0 (encodeInput config rounding input) index) ≤
      componentNorm
          (decodeVector config 0 (encodeInput config rounding input) index -
            rationalInputToComplex input index) +
        componentNorm (rationalInputToComplex input index) :=
      componentNorm_le_add_error _ _
    _ ≤ quantum (config.boundaryFormat 0) + magnitude := by
      apply add_le_add
      · simpa [decodeVector, encodeInput, rationalInputToComplex] using
          (encodeComplex_componentError rounding (config.boundaryFormat 0)
            (input index))
      · exact (componentNorm_le_norm _).trans (inputMagnitude index)
    _ = magnitude + quantum (config.boundaryFormat 0) := by ring

/-- Quantization increases a uniform Euclidean input-magnitude bound by at
most `sqrt 2` times one component LSB. -/
theorem encodeInput_magnitudeBound (config : Config depth)
    (rounding : FixedPoint.RoundingMode)
    (input : Fin (2 ^ depth) → HTFFT.Complex Rat) (magnitude : ℝ)
    (inputMagnitude : MagnitudeBound magnitude
      (rationalInputToComplex input)) :
    MagnitudeBound
      (magnitude + Real.sqrt 2 * quantum (config.boundaryFormat 0))
      (decodeVector config 0 (encodeInput config rounding input)) := by
  intro index
  calc
    ‖decodeVector config 0 (encodeInput config rounding input) index‖ ≤
      ‖decodeVector config 0 (encodeInput config rounding input) index -
          rationalInputToComplex input index‖ +
        ‖rationalInputToComplex input index‖ := by
      simpa only [sub_add_cancel] using
        (norm_add_le
          (decodeVector config 0 (encodeInput config rounding input) index -
            rationalInputToComplex input index)
          (rationalInputToComplex input index))
    _ ≤ Real.sqrt 2 * quantum (config.boundaryFormat 0) + magnitude :=
      add_le_add (encodeInput_within config rounding input index)
        (inputMagnitude index)
    _ = magnitude + Real.sqrt 2 * quantum (config.boundaryFormat 0) := by ring

/-- Standard pre-quantization corollary for a rational-complex input encoded
with the project's quantizer. -/
theorem layeredFFT_within_encodedInput (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (rounding : FixedPoint.RoundingMode)
    (input : Fin (2 ^ depth) → HTFFT.Complex Rat)
    (inputMagnitude : ℝ) (inputMagnitudeNonnegative : 0 ≤ inputMagnitude)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (exactInputMagnitude : MagnitudeBound inputMagnitude
      (rationalInputToComplex input))
    (noOverflow : NoOverflow config table (encodeInput config rounding input)) :
    Within
      (boundsAt config twiddleError
        { magnitude := inputMagnitude
          error := Real.sqrt 2 * quantum (config.boundaryFormat 0) }
        (Fin.last depth)).error
      (decodeVector config (Fin.last depth)
        (layeredFFT config table (encodeInput config rounding input)))
      (Exact.layeredFFT depth (rationalInputToComplex input)) := by
  apply layeredFFT_within_quantizedInput config table twiddleError
    (encodeInput config rounding input) (rationalInputToComplex input)
    inputMagnitude (Real.sqrt 2 * quantum (config.boundaryFormat 0))
    inputMagnitudeNonnegative
      (mul_nonneg (Real.sqrt_nonneg _)
        (quantum_nonnegative (config.boundaryFormat 0)))
    twiddleAccuracy exactInputMagnitude
  · exact encodeInput_within config rounding input
  · exact noOverflow

/-- The numerical theorem with the certified exact-network/DFT equality
substituted at the final boundary. -/
theorem layeredFFT_pointwise_dft (config : Config depth)
    (table : TwiddleTable depth) (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (noOverflow : NoOverflow config table fixedInput)
    (index : Fin (2 ^ depth)) :
    ‖decodeVector config (Fin.last depth)
            (layeredFFT config table fixedInput) index -
          ZMod.dft (Exact.toZModVector exactInput)
            (Exact.zmodIndexEquiv depth index)‖ ≤
      (boundsAt config twiddleError initial (Fin.last depth)).error := by
  have bounded := layeredFFT_within config table twiddleError fixedInput
    exactInput initial initialNonnegative twiddleAccuracy inputMagnitude
    inputWithin noOverflow index
  rw [Exact.layeredFFT_agreesWithDFT] at bounded
  exact bounded

end HTFFT.Fixed
