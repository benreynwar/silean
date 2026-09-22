import HTFFT.Fixed.Layered
import HTFFT.FixedPoint.Correctness
import Mathlib.Tactic

namespace HTFFT.Fixed

open HTFFT.FixedPoint

@[simp]
theorem rationalComplexToComplex_re (value : HTFFT.Complex Rat) :
    (rationalComplexToComplex value).re = (value.real : ℝ) := by
  simp [rationalComplexToComplex]

@[simp]
theorem rationalComplexToComplex_im (value : HTFFT.Complex Rat) :
    (rationalComplexToComplex value).im = (value.imag : ℝ) := by
  simp [rationalComplexToComplex]

@[simp]
theorem rationalComplexToComplex_add (left right : HTFFT.Complex Rat) :
    rationalComplexToComplex (left + right) =
      rationalComplexToComplex left + rationalComplexToComplex right := by
  apply Complex.ext <;> simp

@[simp]
theorem rationalComplexToComplex_sub (left right : HTFFT.Complex Rat) :
    rationalComplexToComplex (left - right) =
      rationalComplexToComplex left - rationalComplexToComplex right := by
  apply Complex.ext <;> simp

@[simp]
theorem rationalComplexToComplex_mul (left right : HTFFT.Complex Rat) :
    rationalComplexToComplex (left * right) =
      rationalComplexToComplex left * rationalComplexToComplex right := by
  apply Complex.ext <;> simp

@[simp]
theorem quantum_eq_cast (format : Format) :
    ((format.quantum : Rat) : ℝ) = quantum format := by
  rw [Format.quantum, Rat.cast_divInt]
  simp [quantum, Format.scale]

theorem quantum_nonnegative (format : Format) : 0 ≤ quantum format := by
  unfold quantum
  positivity

theorem componentArithmeticError_nonnegative
    (config : Butterfly.Fixed.Config) :
    0 ≤ componentArithmeticError config := by
  unfold componentArithmeticError
  have product := quantum_nonnegative config.productFormat
  have output := quantum_nonnegative config.outputFormat
  positivity

theorem arithmeticError_nonnegative (config : Butterfly.Fixed.Config) :
    0 ≤ arithmeticError config := by
  unfold arithmeticError
  positivity [componentArithmeticError_nonnegative config]

theorem encodeComplex_componentError (mode : RoundingMode) (format : Format)
    (value : HTFFT.Complex Rat) :
    componentNorm
        (decodeComplex format (FixedPoint.encodeComplex mode format value) -
          rationalComplexToComplex value) ≤
      quantum format := by
  have realBound := decode_encode_error mode format value.real
  have imagBound := decode_encode_error mode format value.imag
  have realBound' :
      |((FixedPoint.decode format
          (FixedPoint.encode mode format value.real) - value.real : Rat) : ℝ)| ≤
        ((format.quantum : Rat) : ℝ) := by
    exact_mod_cast realBound
  have imagBound' :
      |((FixedPoint.decode format
          (FixedPoint.encode mode format value.imag) - value.imag : Rat) : ℝ)| ≤
        ((format.quantum : Rat) : ℝ) := by
    exact_mod_cast imagBound
  apply max_le
  · simpa [decodeComplex, FixedPoint.decodeComplex, FixedPoint.encodeComplex,
      HTFFT.Complex.map] using
      realBound'
  · simpa [decodeComplex, FixedPoint.decodeComplex, FixedPoint.encodeComplex,
      HTFFT.Complex.map] using
      imagBound'

theorem componentNorm_nonnegative (value : ℂ) :
    0 ≤ componentNorm value := by
  simp [componentNorm]

theorem abs_re_le_componentNorm (value : ℂ) :
    |value.re| ≤ componentNorm value := by
  exact le_max_left _ _

theorem abs_im_le_componentNorm (value : ℂ) :
    |value.im| ≤ componentNorm value := by
  exact le_max_right _ _

@[simp]
theorem componentNorm_zero : componentNorm 0 = 0 := by
  simp [componentNorm]

@[simp]
theorem componentNorm_neg (value : ℂ) :
    componentNorm (-value) = componentNorm value := by
  simp [componentNorm]

theorem componentNorm_add_le (left right : ℂ) :
    componentNorm (left + right) ≤
      componentNorm left + componentNorm right := by
  apply max_le
  · rw [Complex.add_re]
    exact (abs_add_le _ _).trans (add_le_add
      (abs_re_le_componentNorm left) (abs_re_le_componentNorm right))
  · rw [Complex.add_im]
    exact (abs_add_le _ _).trans (add_le_add
      (abs_im_le_componentNorm left) (abs_im_le_componentNorm right))

theorem componentNorm_sub_le (left right : ℂ) :
    componentNorm (left - right) ≤
      componentNorm left + componentNorm right := by
  rw [sub_eq_add_neg]
  calc
    componentNorm (left + -right) ≤
        componentNorm left + componentNorm (-right) :=
      componentNorm_add_le _ _
    _ = componentNorm left + componentNorm right := by
      rw [componentNorm_neg]

theorem componentNorm_le_add_error (actual exact : ℂ) :
    componentNorm actual ≤
      componentNorm (actual - exact) + componentNorm exact := by
  calc
    componentNorm actual = componentNorm ((actual - exact) + exact) := by
      congr 1
      ring
    _ ≤ componentNorm (actual - exact) + componentNorm exact :=
      componentNorm_add_le _ _

theorem componentNorm_le_norm (value : ℂ) : componentNorm value ≤ ‖value‖ := by
  exact max_le (Complex.abs_re_le_norm value) (Complex.abs_im_le_norm value)

theorem MagnitudeBound.component {values : Fin count → ℂ} {bound : ℝ}
    (bounded : MagnitudeBound bound values) :
    ComponentMagnitudeBound bound values := by
  intro index
  exact (componentNorm_le_norm _).trans (bounded index)

/-- Euclidean complex magnitude is at most `sqrt 2` times the maximum
component magnitude. This is the sole conversion needed at componentwise
fixed-point rounding and interval-certificate boundaries. -/
theorem norm_le_sqrtTwo_mul_componentNorm (value : ℂ) :
    ‖value‖ ≤ Real.sqrt 2 * componentNorm value := by
  let bound := componentNorm value
  have boundNonnegative : 0 ≤ bound := componentNorm_nonnegative value
  have realBound := abs_re_le_componentNorm value
  have imagBound := abs_im_le_componentNorm value
  have realSquare : value.re ^ 2 ≤ bound ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) boundNonnegative).2 realBound
  have imagSquare : value.im ^ 2 ≤ bound ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) boundNonnegative).2 imagBound
  have squares : value.re ^ 2 + value.im ^ 2 ≤ 2 * bound ^ 2 := by
    linarith
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  calc
    Real.sqrt (value.re ^ 2 + value.im ^ 2) ≤
        Real.sqrt (2 * bound ^ 2) := Real.sqrt_le_sqrt squares
    _ = Real.sqrt 2 * bound := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq_eq_abs, abs_of_nonneg boundNonnegative]

/-- Componentwise quantization error converted to Euclidean complex
magnitude. -/
theorem encodeComplex_error (mode : RoundingMode) (format : Format)
    (value : HTFFT.Complex Rat) :
    ‖decodeComplex format (FixedPoint.encodeComplex mode format value) -
        rationalComplexToComplex value‖ ≤
      Real.sqrt 2 * quantum format := by
  exact (norm_le_sqrtTwo_mul_componentNorm _).trans
    (mul_le_mul_of_nonneg_left
      (encodeComplex_componentError mode format value) (Real.sqrt_nonneg _))

theorem norm_sub_triangle (first middle last : ℂ) :
    ‖first - last‖ ≤ ‖first - middle‖ + ‖middle - last‖ := by
  calc
    ‖first - last‖ = ‖(first - middle) + (middle - last)‖ := by
      congr 1
      ring
    _ ≤ ‖first - middle‖ + ‖middle - last‖ := norm_add_le _ _

@[simp]
theorem norm_exactTwiddle (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    ‖exactTwiddle stage offset‖ = 1 := by
  rw [exactTwiddle, Exact.twiddle, ZMod.stdAddChar_apply, Circle.norm_coe]

theorem norm_ideal_upper_le {a b twiddle : ℂ} {magnitude : ℝ}
    (aBound : ‖a‖ ≤ magnitude) (bBound : ‖b‖ ≤ magnitude)
    (twiddleNorm : ‖twiddle‖ = 1) :
    ‖a + twiddle * b‖ ≤ 2 * magnitude := by
  calc
    ‖a + twiddle * b‖ ≤ ‖a‖ + ‖twiddle * b‖ := norm_add_le _ _
    _ = ‖a‖ + ‖twiddle‖ * ‖b‖ := by rw [norm_mul]
    _ ≤ magnitude + 1 * magnitude := by
      rw [twiddleNorm]
      simpa using add_le_add aBound bBound
    _ = 2 * magnitude := by ring

theorem norm_ideal_lower_le {a b twiddle : ℂ} {magnitude : ℝ}
    (aBound : ‖a‖ ≤ magnitude) (bBound : ‖b‖ ≤ magnitude)
    (twiddleNorm : ‖twiddle‖ = 1) :
    ‖a - twiddle * b‖ ≤ 2 * magnitude := by
  calc
    ‖a - twiddle * b‖ ≤ ‖a‖ + ‖twiddle * b‖ := norm_sub_le _ _
    _ = ‖a‖ + ‖twiddle‖ * ‖b‖ := by rw [norm_mul]
    _ ≤ magnitude + 1 * magnitude := by
      rw [twiddleNorm]
      simpa using add_le_add aBound bBound
    _ = 2 * magnitude := by ring

/-- Perturbing both operands of a complex product in Euclidean magnitude.
The exact right operand is a unit twiddle. -/
theorem norm_mul_approximation_le
    (actualLeft exactLeft actualRight exactRight : ℂ)
    (magnitude error twiddleError : ℝ)
    (magnitudeNonnegative : 0 ≤ magnitude)
    (errorNonnegative : 0 ≤ error)
    (_twiddleErrorNonnegative : 0 ≤ twiddleError)
    (leftMagnitude : ‖exactLeft‖ ≤ magnitude)
    (rightNorm : ‖exactRight‖ = 1)
    (leftClose : ‖actualLeft - exactLeft‖ ≤ error)
    (rightClose : ‖actualRight - exactRight‖ ≤ twiddleError) :
    ‖actualLeft * actualRight - exactLeft * exactRight‖ ≤
      error * (1 + twiddleError) + magnitude * twiddleError := by
  have actualRightMagnitude : ‖actualRight‖ ≤ 1 + twiddleError := by
    calc
      ‖actualRight‖ ≤ ‖actualRight - exactRight‖ + ‖exactRight‖ := by
        simpa only [sub_add_cancel] using
          (norm_add_le (actualRight - exactRight) exactRight)
      _ ≤ twiddleError + 1 := add_le_add rightClose (le_of_eq rightNorm)
      _ = 1 + twiddleError := by ring
  have firstProduct :
      ‖(actualLeft - exactLeft) * actualRight‖ ≤
        error * (1 + twiddleError) := by
    rw [norm_mul]
    exact mul_le_mul leftClose actualRightMagnitude
      (norm_nonneg actualRight) errorNonnegative
  have secondProduct :
      ‖exactLeft * (actualRight - exactRight)‖ ≤
        magnitude * twiddleError := by
    rw [norm_mul]
    exact mul_le_mul leftMagnitude rightClose
      (norm_nonneg (actualRight - exactRight)) magnitudeNonnegative
  calc
    ‖actualLeft * actualRight - exactLeft * exactRight‖ =
        ‖(actualLeft - exactLeft) * actualRight +
          exactLeft * (actualRight - exactRight)‖ := by
      congr 1
      ring
    _ ≤ ‖(actualLeft - exactLeft) * actualRight‖ +
          ‖exactLeft * (actualRight - exactRight)‖ := norm_add_le _ _
    _ ≤ error * (1 + twiddleError) + magnitude * twiddleError :=
      add_le_add firstProduct secondProduct

theorem norm_butterfly_upper_approximation_le
    (actualA exactA actualB exactB actualTwiddle exactTwiddle : ℂ)
    (magnitude error twiddleError : ℝ)
    (magnitudeNonnegative : 0 ≤ magnitude)
    (errorNonnegative : 0 ≤ error)
    (twiddleErrorNonnegative : 0 ≤ twiddleError)
    (bMagnitude : ‖exactB‖ ≤ magnitude)
    (exactTwiddleNorm : ‖exactTwiddle‖ = 1)
    (aClose : ‖actualA - exactA‖ ≤ error)
    (bClose : ‖actualB - exactB‖ ≤ error)
    (twiddleClose : ‖actualTwiddle - exactTwiddle‖ ≤ twiddleError) :
    ‖(actualA + actualB * actualTwiddle) -
        (exactA + exactTwiddle * exactB)‖ ≤
      (2 + twiddleError) * error + magnitude * twiddleError := by
  have productClose := norm_mul_approximation_le actualB exactB
    actualTwiddle exactTwiddle magnitude error twiddleError
    magnitudeNonnegative errorNonnegative twiddleErrorNonnegative bMagnitude
    exactTwiddleNorm bClose twiddleClose
  calc
    ‖(actualA + actualB * actualTwiddle) -
        (exactA + exactTwiddle * exactB)‖ =
      ‖(actualA - exactA) +
        (actualB * actualTwiddle - exactB * exactTwiddle)‖ := by
        congr 1
        ring
    _ ≤ ‖actualA - exactA‖ +
          ‖actualB * actualTwiddle - exactB * exactTwiddle‖ := norm_add_le _ _
    _ ≤ error +
          (error * (1 + twiddleError) + magnitude * twiddleError) :=
      add_le_add aClose productClose
    _ = (2 + twiddleError) * error + magnitude * twiddleError := by ring

theorem norm_butterfly_lower_approximation_le
    (actualA exactA actualB exactB actualTwiddle exactTwiddle : ℂ)
    (magnitude error twiddleError : ℝ)
    (magnitudeNonnegative : 0 ≤ magnitude)
    (errorNonnegative : 0 ≤ error)
    (twiddleErrorNonnegative : 0 ≤ twiddleError)
    (bMagnitude : ‖exactB‖ ≤ magnitude)
    (exactTwiddleNorm : ‖exactTwiddle‖ = 1)
    (aClose : ‖actualA - exactA‖ ≤ error)
    (bClose : ‖actualB - exactB‖ ≤ error)
    (twiddleClose : ‖actualTwiddle - exactTwiddle‖ ≤ twiddleError) :
    ‖(actualA - actualB * actualTwiddle) -
        (exactA - exactTwiddle * exactB)‖ ≤
      (2 + twiddleError) * error + magnitude * twiddleError := by
  have productClose := norm_mul_approximation_le actualB exactB
    actualTwiddle exactTwiddle magnitude error twiddleError
    magnitudeNonnegative errorNonnegative twiddleErrorNonnegative bMagnitude
    exactTwiddleNorm bClose twiddleClose
  calc
    ‖(actualA - actualB * actualTwiddle) -
        (exactA - exactTwiddle * exactB)‖ =
      ‖(actualA - exactA) -
        (actualB * actualTwiddle - exactB * exactTwiddle)‖ := by
        congr 1
        ring
    _ ≤ ‖actualA - exactA‖ +
          ‖actualB * actualTwiddle - exactB * exactTwiddle‖ := norm_sub_le _ _
    _ ≤ error +
          (error * (1 + twiddleError) + magnitude * twiddleError) :=
      add_le_add aClose productClose
    _ = (2 + twiddleError) * error + magnitude * twiddleError := by ring

end HTFFT.Fixed
