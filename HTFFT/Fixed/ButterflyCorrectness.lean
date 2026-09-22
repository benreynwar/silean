import HTFFT.Fixed.Error
import HTFFT.FixedPoint.Correctness
import Mathlib.Tactic

namespace HTFFT.Butterfly.Fixed

open HTFFT
open HTFFT.FixedPoint

theorem rationalAbs_eq_abs (value : Rat) : rationalAbs value = |value| := by
  unfold rationalAbs
  by_cases negative : value < 0
  · rw [if_pos negative, abs_of_neg negative]
  · rw [if_neg negative, abs_of_nonneg (le_of_not_gt negative)]

/-- Componentwise rescaling inherits the scalar one-LSB bound. -/
theorem rescaleComplex_within (rounding : RoundingMode)
    (source destination : Format) (value : HTFFT.Complex Int) :
    componentwiseWithin destination.quantum
      (FixedPoint.decodeComplex destination
        (rescaleComplex rounding source destination value))
      (FixedPoint.decodeComplex source value) := by
  constructor
  · rw [rationalAbs_eq_abs]
    exact decode_rescale_error rounding source destination value.real
  · rw [rationalAbs_eq_abs]
    exact decode_rescale_error rounding source destination value.imag

/-- Decoding a fused, rounded complex product differs from multiplying the
decoded operands by at most one product-format LSB per component. -/
theorem multiplyRounded_within (config : Config)
    (left twiddle : HTFFT.Complex Int) :
    componentwiseWithin config.productFormat.quantum
      (FixedPoint.decodeComplex config.productFormat
        (multiplyRounded config left twiddle))
      (FixedPoint.decodeComplex config.dataFormat left *
        FixedPoint.decodeComplex config.twiddleFormat twiddle) := by
  let source : Format :=
    ⟨0, config.dataFormat.fractionalBits +
      config.twiddleFormat.fractionalBits⟩
  constructor
  · rw [rationalAbs_eq_abs]
    have rounded := decode_rescale_error config.rounding source
      config.productFormat
      (left.real * twiddle.real - left.imag * twiddle.imag)
    simpa [multiplyRounded, source, FixedPoint.decodeComplex,
      HTFFT.Complex.map, HTFFT.Complex.mul_real, decode_sub, decode_mul] using
      rounded
  · rw [rationalAbs_eq_abs]
    have rounded := decode_rescale_error config.rounding source
      config.productFormat
      (left.real * twiddle.imag + left.imag * twiddle.real)
    simpa [multiplyRounded, source, FixedPoint.decodeComplex,
      HTFFT.Complex.map, HTFFT.Complex.mul_imag, decode_add, decode_mul] using
      rounded

theorem wrapComplex_eq_of_fits {format : Format}
    {value : HTFFT.Complex Int} (fits : ComplexFits format value) :
    wrapComplex format value = value := by
  rcases fits with ⟨realFits, imagFits⟩
  rcases value with ⟨real, imag⟩
  change { real := wrapSigned format.width real
           imag := wrapSigned format.width imag } =
    ({ real := real, imag := imag } : HTFFT.Complex Int)
  rw [wrapSigned_eq_of_format_fits realFits,
    wrapSigned_eq_of_format_fits imagFits]

theorem alignedA_eq_rounded_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    alignedA config a = alignedARounded config a := by
  apply wrapComplex_eq_of_fits
  exact noOverflow.2.2.2.1

theorem multiply_eq_rounded_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    multiply config b twiddle = multiplyRounded config b twiddle := by
  apply wrapComplex_eq_of_fits
  exact noOverflow.2.2.2.2.1

theorem alignedA_within_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    componentwiseWithin config.productFormat.quantum
      (FixedPoint.decodeComplex config.productFormat (alignedA config a))
      (FixedPoint.decodeComplex config.dataFormat a) := by
  rw [alignedA_eq_rounded_of_noOverflow noOverflow]
  exact rescaleComplex_within config.rounding config.dataFormat
    config.productFormat a

theorem multiply_within_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    componentwiseWithin config.productFormat.quantum
      (FixedPoint.decodeComplex config.productFormat
        (multiply config b twiddle))
      (FixedPoint.decodeComplex config.dataFormat b *
        FixedPoint.decodeComplex config.twiddleFormat twiddle) := by
  rw [multiply_eq_rounded_of_noOverflow noOverflow]
  exact multiplyRounded_within config b twiddle

theorem butterfly_eq_outputRounded_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    butterfly config a b twiddle = outputRounded config a b twiddle := by
  unfold butterfly
  dsimp only
  rw [wrapComplex_eq_of_fits noOverflow.2.2.2.2.2.1,
    wrapComplex_eq_of_fits noOverflow.2.2.2.2.2.2]

@[simp]
theorem decodeResult_upper (config : Config) (result : Result Int) :
    (decodeResult config result).upper =
      FixedPoint.decodeComplex config.outputFormat result.upper := rfl

@[simp]
theorem decodeResult_lower (config : Config) (result : Result Int) :
    (decodeResult config result).lower =
      FixedPoint.decodeComplex config.outputFormat result.lower := rfl

@[simp]
theorem exactDecodedInputs_upper (config : Config)
    (a b twiddle : HTFFT.Complex Int) :
    (exactDecodedInputs config a b twiddle).upper =
      FixedPoint.decodeComplex config.dataFormat a +
        FixedPoint.decodeComplex config.dataFormat b *
          FixedPoint.decodeComplex config.twiddleFormat twiddle := rfl

@[simp]
theorem exactDecodedInputs_lower (config : Config)
    (a b twiddle : HTFFT.Complex Int) :
    (exactDecodedInputs config a b twiddle).lower =
      FixedPoint.decodeComplex config.dataFormat a -
        FixedPoint.decodeComplex config.dataFormat b *
          FixedPoint.decodeComplex config.twiddleFormat twiddle := rfl

@[simp]
theorem outputRounded_upper (config : Config)
    (a b twiddle : HTFFT.Complex Int) :
    (outputRounded config a b twiddle).upper =
      rescaleComplex config.rounding config.productFormat config.outputFormat
        (alignedA config a + multiply config b twiddle) := rfl

@[simp]
theorem outputRounded_lower (config : Config)
    (a b twiddle : HTFFT.Complex Int) :
    (outputRounded config a b twiddle).lower =
      rescaleComplex config.rounding config.productFormat config.outputFormat
        (alignedA config a - multiply config b twiddle) := rfl

private theorem abs_add_approximation
    (actual roundedLeft roundedRight exactLeft exactRight
      outputError inputError : Rat)
    (outputClose : |actual - (roundedLeft + roundedRight)| ≤ outputError)
    (leftClose : |roundedLeft - exactLeft| ≤ inputError)
    (rightClose : |roundedRight - exactRight| ≤ inputError) :
    |actual - (exactLeft + exactRight)| ≤
      2 * inputError + outputError := by
  rw [abs_le] at outputClose leftClose rightClose ⊢
  constructor <;> linarith

private theorem abs_sub_approximation
    (actual roundedLeft roundedRight exactLeft exactRight
      outputError inputError : Rat)
    (outputClose : |actual - (roundedLeft - roundedRight)| ≤ outputError)
    (leftClose : |roundedLeft - exactLeft| ≤ inputError)
    (rightClose : |roundedRight - exactRight| ≤ inputError) :
    |actual - (exactLeft - exactRight)| ≤
      2 * inputError + outputError := by
  rw [abs_le] at outputClose leftClose rightClose ⊢
  constructor <;> linarith

/-- The complete local arithmetic theorem.  In the absence of overflow, each
component of either decoded butterfly output differs from the exact butterfly
on the decoded input and stored twiddle by at most two product LSBs plus one
output LSB. -/
theorem butterfly_within_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    resultWithin
      (2 * config.productFormat.quantum + config.outputFormat.quantum)
      (decodeResult config (butterfly config a b twiddle))
      (exactDecodedInputs config a b twiddle) := by
  let prepared := alignedA config a
  let rotated := multiply config b twiddle
  let decodedPrepared := FixedPoint.decodeComplex config.productFormat prepared
  let decodedRotated := FixedPoint.decodeComplex config.productFormat rotated
  let exactA := FixedPoint.decodeComplex config.dataFormat a
  let exactRotated := FixedPoint.decodeComplex config.dataFormat b *
    FixedPoint.decodeComplex config.twiddleFormat twiddle
  have preparedClose := alignedA_within_of_noOverflow noOverflow
  have rotatedClose := multiply_within_of_noOverflow noOverflow
  have upperRounded := rescaleComplex_within config.rounding
    config.productFormat config.outputFormat (prepared + rotated)
  have lowerRounded := rescaleComplex_within config.rounding
    config.productFormat config.outputFormat (prepared - rotated)
  have preparedRealClose :
      |decodedPrepared.real - exactA.real| ≤
        config.productFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [prepared, decodedPrepared, exactA] using preparedClose.1
  have preparedImagClose :
      |decodedPrepared.imag - exactA.imag| ≤
        config.productFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [prepared, decodedPrepared, exactA] using preparedClose.2
  have rotatedRealClose :
      |decodedRotated.real - exactRotated.real| ≤
        config.productFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [rotated, decodedRotated, exactRotated] using rotatedClose.1
  have rotatedImagClose :
      |decodedRotated.imag - exactRotated.imag| ≤
        config.productFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [rotated, decodedRotated, exactRotated] using rotatedClose.2
  have upperRealClose :
      |(FixedPoint.decodeComplex config.outputFormat
            (rescaleComplex config.rounding config.productFormat
              config.outputFormat (prepared + rotated))).real -
          (decodedPrepared.real + decodedRotated.real)| ≤
        config.outputFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [FixedPoint.decodeComplex_add, HTFFT.Complex.add_real,
      decodedPrepared, decodedRotated] using upperRounded.1
  have upperImagClose :
      |(FixedPoint.decodeComplex config.outputFormat
            (rescaleComplex config.rounding config.productFormat
              config.outputFormat (prepared + rotated))).imag -
          (decodedPrepared.imag + decodedRotated.imag)| ≤
        config.outputFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [FixedPoint.decodeComplex_add, HTFFT.Complex.add_imag,
      decodedPrepared, decodedRotated] using upperRounded.2
  have lowerRealClose :
      |(FixedPoint.decodeComplex config.outputFormat
            (rescaleComplex config.rounding config.productFormat
              config.outputFormat (prepared - rotated))).real -
          (decodedPrepared.real - decodedRotated.real)| ≤
        config.outputFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [FixedPoint.decodeComplex_sub, HTFFT.Complex.sub_real,
      decodedPrepared, decodedRotated] using lowerRounded.1
  have lowerImagClose :
      |(FixedPoint.decodeComplex config.outputFormat
            (rescaleComplex config.rounding config.productFormat
              config.outputFormat (prepared - rotated))).imag -
          (decodedPrepared.imag - decodedRotated.imag)| ≤
        config.outputFormat.quantum := by
    rw [← rationalAbs_eq_abs]
    simpa only [FixedPoint.decodeComplex_sub, HTFFT.Complex.sub_imag,
      decodedPrepared, decodedRotated] using lowerRounded.2
  rw [butterfly_eq_outputRounded_of_noOverflow noOverflow]
  simp only [resultWithin, componentwiseWithin, decodeResult_upper,
    decodeResult_lower, exactDecodedInputs_upper, exactDecodedInputs_lower,
    outputRounded_upper, outputRounded_lower, HTFFT.Complex.add_real,
    HTFFT.Complex.add_imag, HTFFT.Complex.sub_real, HTFFT.Complex.sub_imag]
  constructor
  · constructor
    · rw [rationalAbs_eq_abs]
      exact abs_add_approximation
        _ decodedPrepared.real decodedRotated.real exactA.real exactRotated.real
        (outputError := config.outputFormat.quantum)
        (inputError := config.productFormat.quantum)
        upperRealClose preparedRealClose rotatedRealClose
    · rw [rationalAbs_eq_abs]
      exact abs_add_approximation
        _ decodedPrepared.imag decodedRotated.imag exactA.imag exactRotated.imag
        (outputError := config.outputFormat.quantum)
        (inputError := config.productFormat.quantum)
        upperImagClose preparedImagClose rotatedImagClose
  · constructor
    · rw [rationalAbs_eq_abs]
      exact abs_sub_approximation
        _ decodedPrepared.real decodedRotated.real exactA.real exactRotated.real
        (outputError := config.outputFormat.quantum)
        (inputError := config.productFormat.quantum)
        lowerRealClose preparedRealClose rotatedRealClose
    · rw [rationalAbs_eq_abs]
      exact abs_sub_approximation
        _ decodedPrepared.imag decodedRotated.imag exactA.imag exactRotated.imag
        (outputError := config.outputFormat.quantum)
        (inputError := config.productFormat.quantum)
        lowerImagClose preparedImagClose rotatedImagClose

theorem hasLocalErrorBound (config : Config) :
    HasLocalErrorBound config
      (2 * config.productFormat.quantum + config.outputFormat.quantum) := by
  constructor
  · have productQuantumPositive : (0 : Rat) < config.productFormat.quantum := by
      rw [Format.quantum, Rat.divInt_eq_div]
      apply div_pos
      · norm_num
      · exact_mod_cast config.productFormat.scale_pos
    have outputQuantumPositive : (0 : Rat) < config.outputFormat.quantum := by
      rw [Format.quantum, Rat.divInt_eq_div]
      apply div_pos
      · norm_num
      · exact_mod_cast config.outputFormat.scale_pos
    positivity
  · intro a b twiddle noOverflow
    exact butterfly_within_of_noOverflow noOverflow

/-- Decode both fixed-point outputs into Mathlib complex numbers. -/
noncomputable def decodeResultComplex (config : Config) (result : Result Int) :
    ℂ × ℂ :=
  (HTFFT.Fixed.decodeComplex config.outputFormat result.upper,
    HTFFT.Fixed.decodeComplex config.outputFormat result.lower)

/-- The ideal complex butterfly on the values denoted by the fixed input and
stored twiddle. -/
noncomputable def exactDecodedInputsComplex (config : Config)
    (a b twiddle : HTFFT.Complex Int) : ℂ × ℂ :=
  let decodedA := HTFFT.Fixed.decodeComplex config.dataFormat a
  let rotated := HTFFT.Fixed.decodeComplex config.dataFormat b *
    HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle
  (decodedA + rotated, decodedA - rotated)

private theorem rat_abs_cast_le {value bound : Rat}
    (bounded : |value| ≤ bound) :
    |(value : ℝ)| ≤ (bound : ℝ) := by
  exact_mod_cast bounded

/-- Componentwise real-complex form of the local arithmetic theorem. This is
the fixed-point boundary fact from which the Euclidean theorem is derived. -/
theorem butterfly_within_component_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    HTFFT.Fixed.componentNorm
          ((decodeResultComplex config (butterfly config a b twiddle)).1 -
            (exactDecodedInputsComplex config a b twiddle).1) ≤
        HTFFT.Fixed.componentArithmeticError config ∧
      HTFFT.Fixed.componentNorm
          ((decodeResultComplex config (butterfly config a b twiddle)).2 -
            (exactDecodedInputsComplex config a b twiddle).2) ≤
        HTFFT.Fixed.componentArithmeticError config := by
  have localBound := butterfly_within_of_noOverflow noOverflow
  rcases localBound with ⟨upper, lower⟩
  rcases upper with ⟨upperReal, upperImag⟩
  rcases lower with ⟨lowerReal, lowerImag⟩
  rw [rationalAbs_eq_abs] at upperReal upperImag lowerReal lowerImag
  have upperReal' := rat_abs_cast_le upperReal
  have upperImag' := rat_abs_cast_le upperImag
  have lowerReal' := rat_abs_cast_le lowerReal
  have lowerImag' := rat_abs_cast_le lowerImag
  constructor <;> apply max_le
  · simpa [decodeResultComplex, exactDecodedInputsComplex,
      HTFFT.Fixed.componentNorm, HTFFT.Fixed.decodeComplex,
      HTFFT.Fixed.componentArithmeticError, decodeResult, exactDecodedInputs,
      mathematical] using upperReal'
  · simpa [decodeResultComplex, exactDecodedInputsComplex,
      HTFFT.Fixed.componentNorm, HTFFT.Fixed.decodeComplex,
      HTFFT.Fixed.componentArithmeticError, decodeResult, exactDecodedInputs,
      mathematical] using upperImag'
  · simpa [decodeResultComplex, exactDecodedInputsComplex,
      HTFFT.Fixed.componentNorm, HTFFT.Fixed.decodeComplex,
      HTFFT.Fixed.componentArithmeticError, decodeResult, exactDecodedInputs,
      mathematical] using lowerReal'
  · simpa [decodeResultComplex, exactDecodedInputsComplex,
      HTFFT.Fixed.componentNorm, HTFFT.Fixed.decodeComplex,
      HTFFT.Fixed.componentArithmeticError, decodeResult, exactDecodedInputs,
      mathematical] using lowerImag'

/-- Euclidean complex-magnitude form of the local arithmetic theorem used by
the network induction. -/
theorem butterfly_within_complex_of_noOverflow {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    (noOverflow : NoOverflow config a b twiddle) :
    ‖(decodeResultComplex config (butterfly config a b twiddle)).1 -
        (exactDecodedInputsComplex config a b twiddle).1‖ ≤
        HTFFT.Fixed.arithmeticError config ∧
      ‖(decodeResultComplex config (butterfly config a b twiddle)).2 -
        (exactDecodedInputsComplex config a b twiddle).2‖ ≤
        HTFFT.Fixed.arithmeticError config := by
  have component := butterfly_within_component_of_noOverflow noOverflow
  constructor
  · exact (HTFFT.Fixed.norm_le_sqrtTwo_mul_componentNorm _).trans
      (mul_le_mul_of_nonneg_left component.1 (Real.sqrt_nonneg _))
  · exact (HTFFT.Fixed.norm_le_sqrtTwo_mul_componentNorm _).trans
      (mul_le_mul_of_nonneg_left component.2 (Real.sqrt_nonneg _))

/-- Local upper-output error propagation, including existing input error,
stored-twiddle error, and fixed-point arithmetic error. -/
theorem butterfly_upper_error {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    {exactA exactB exactTwiddle : ℂ}
    {magnitude error twiddleError : ℝ}
    (magnitudeNonnegative : 0 ≤ magnitude)
    (errorNonnegative : 0 ≤ error)
    (twiddleErrorNonnegative : 0 ≤ twiddleError)
    (bMagnitude : ‖exactB‖ ≤ magnitude)
    (exactTwiddleNorm : ‖exactTwiddle‖ = 1)
    (aClose :
      ‖HTFFT.Fixed.decodeComplex config.dataFormat a - exactA‖ ≤ error)
    (bClose :
      ‖HTFFT.Fixed.decodeComplex config.dataFormat b - exactB‖ ≤ error)
    (twiddleClose :
      ‖HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle - exactTwiddle‖ ≤
        twiddleError)
    (noOverflow : NoOverflow config a b twiddle) :
    ‖HTFFT.Fixed.decodeComplex config.outputFormat
            (butterfly config a b twiddle).upper -
          (exactA + exactTwiddle * exactB)‖ ≤
      (2 + twiddleError) * error + magnitude * twiddleError +
        HTFFT.Fixed.arithmeticError config := by
  have arithmetic :=
    (butterfly_within_complex_of_noOverflow noOverflow).1
  have perturbation := HTFFT.Fixed.norm_butterfly_upper_approximation_le
    (HTFFT.Fixed.decodeComplex config.dataFormat a) exactA
    (HTFFT.Fixed.decodeComplex config.dataFormat b) exactB
    (HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle) exactTwiddle
    magnitude error twiddleError magnitudeNonnegative errorNonnegative
    twiddleErrorNonnegative bMagnitude exactTwiddleNorm aClose bClose
    twiddleClose
  calc
    ‖HTFFT.Fixed.decodeComplex config.outputFormat
            (butterfly config a b twiddle).upper -
          (exactA + exactTwiddle * exactB)‖ ≤
      ‖HTFFT.Fixed.decodeComplex config.outputFormat
              (butterfly config a b twiddle).upper -
            (exactDecodedInputsComplex config a b twiddle).1‖ +
        ‖(exactDecodedInputsComplex config a b twiddle).1 -
            (exactA + exactTwiddle * exactB)‖ :=
      HTFFT.Fixed.norm_sub_triangle _ _ _
    _ ≤ HTFFT.Fixed.arithmeticError config +
          ((2 + twiddleError) * error + magnitude * twiddleError) := by
      apply add_le_add arithmetic
      simpa [exactDecodedInputsComplex] using perturbation
    _ = (2 + twiddleError) * error + magnitude * twiddleError +
          HTFFT.Fixed.arithmeticError config := by ring

/-- Local lower-output counterpart of `butterfly_upper_error`. -/
theorem butterfly_lower_error {config : Config}
    {a b twiddle : HTFFT.Complex Int}
    {exactA exactB exactTwiddle : ℂ}
    {magnitude error twiddleError : ℝ}
    (magnitudeNonnegative : 0 ≤ magnitude)
    (errorNonnegative : 0 ≤ error)
    (twiddleErrorNonnegative : 0 ≤ twiddleError)
    (bMagnitude : ‖exactB‖ ≤ magnitude)
    (exactTwiddleNorm : ‖exactTwiddle‖ = 1)
    (aClose :
      ‖HTFFT.Fixed.decodeComplex config.dataFormat a - exactA‖ ≤ error)
    (bClose :
      ‖HTFFT.Fixed.decodeComplex config.dataFormat b - exactB‖ ≤ error)
    (twiddleClose :
      ‖HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle - exactTwiddle‖ ≤
        twiddleError)
    (noOverflow : NoOverflow config a b twiddle) :
    ‖HTFFT.Fixed.decodeComplex config.outputFormat
            (butterfly config a b twiddle).lower -
          (exactA - exactTwiddle * exactB)‖ ≤
      (2 + twiddleError) * error + magnitude * twiddleError +
        HTFFT.Fixed.arithmeticError config := by
  have arithmetic :=
    (butterfly_within_complex_of_noOverflow noOverflow).2
  have perturbation := HTFFT.Fixed.norm_butterfly_lower_approximation_le
    (HTFFT.Fixed.decodeComplex config.dataFormat a) exactA
    (HTFFT.Fixed.decodeComplex config.dataFormat b) exactB
    (HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle) exactTwiddle
    magnitude error twiddleError magnitudeNonnegative errorNonnegative
    twiddleErrorNonnegative bMagnitude exactTwiddleNorm aClose bClose
    twiddleClose
  calc
    ‖HTFFT.Fixed.decodeComplex config.outputFormat
            (butterfly config a b twiddle).lower -
          (exactA - exactTwiddle * exactB)‖ ≤
      ‖HTFFT.Fixed.decodeComplex config.outputFormat
              (butterfly config a b twiddle).lower -
            (exactDecodedInputsComplex config a b twiddle).2‖ +
        ‖(exactDecodedInputsComplex config a b twiddle).2 -
            (exactA - exactTwiddle * exactB)‖ :=
      HTFFT.Fixed.norm_sub_triangle _ _ _
    _ ≤ HTFFT.Fixed.arithmeticError config +
          ((2 + twiddleError) * error + magnitude * twiddleError) := by
      apply add_le_add arithmetic
      simpa [exactDecodedInputsComplex] using perturbation
    _ = (2 + twiddleError) * error + magnitude * twiddleError +
          HTFFT.Fixed.arithmeticError config := by ring

end HTFFT.Butterfly.Fixed
