import HTFFT.Fixed.TwiddleGenerator
import HTFFT.FixedPoint.Range
import HTFFT.Exact.DFT
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace HTFFT.Fixed.TwiddleGenerator

open scoped BigOperators
open HTFFT HTFFT.FixedPoint
open Filter

@[simp] private theorem cast_atanSeries (x : Rat) (terms : Nat) :
    (atanSeries x terms : ℝ) =
      ∑ term ∈ Finset.range terms,
        (-1 : ℝ) ^ term *
          ((x : ℝ) ^ (2 * term + 1) / (2 * term + 1)) := by
  simp [atanSeries, mul_div_assoc]

private theorem arctanTerm_antitone (x : ℝ)
    (x_nonnegative : 0 ≤ x) (x_le_one : x ≤ 1) :
    Antitone (fun term : Nat => x ^ (2 * term + 1) / (2 * term + 1)) := by
  intro first second order
  have powerOrder : 2 * first + 1 ≤ 2 * second + 1 := by omega
  have powerNonnegative : 0 ≤ x ^ (2 * first + 1) := by positivity
  calc
    x ^ (2 * second + 1) / (2 * second + 1) ≤
        x ^ (2 * first + 1) / (2 * second + 1) := by
      apply div_le_div_of_nonneg_right
      · exact pow_le_pow_of_le_one x_nonnegative x_le_one powerOrder
      · positivity
    _ ≤ x ^ (2 * first + 1) / (2 * first + 1) := by
      apply div_le_div_of_nonneg_left powerNonnegative
      · positivity
      · exact_mod_cast powerOrder

private theorem atanSeries_odd_error (x : Rat)
    (x_positive : (0 : ℝ) < x) (x_lt_one : (x : ℝ) < 1)
    (iterations : Nat) :
    0 ≤ (atanSeries x (2 * iterations + 1) : ℝ) - Real.arctan x ∧
      (atanSeries x (2 * iterations + 1) : ℝ) - Real.arctan x ≤
        (x : ℝ) ^ (2 * (2 * iterations) + 1) /
          (2 * (2 * iterations) + 1) := by
  let term : Nat → ℝ := fun index =>
    (x : ℝ) ^ (2 * index + 1) / (2 * index + 1)
  have antitone : Antitone term :=
    arctanTerm_antitone (x : ℝ) x_positive.le x_lt_one.le
  have normLt : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos x_positive]
    exact x_lt_one
  have sumTends : Tendsto
      (fun count => ∑ index ∈ Finset.range count, (-1 : ℝ) ^ index * term index)
      Filter.atTop (nhds (Real.arctan x)) := by
    convert (Real.hasSum_arctan (x := (x : ℝ)) normLt).tendsto_sum_nat using 1
    funext count
    apply Finset.sum_congr rfl
    intro index _
    dsimp [term]
    push_cast
    ring
  have upper := antitone.tendsto_le_alternating_series sumTends iterations
  have lower := antitone.alternating_series_le_tendsto sumTends iterations
  constructor
  · rw [cast_atanSeries]
    simpa [term] using sub_nonneg.mpr upper
  · rw [cast_atanSeries]
    rw [show 2 * iterations + 1 = 2 * iterations + 1 by rfl]
    have difference :
        (∑ index ∈ Finset.range (2 * iterations + 1),
            (-1 : ℝ) ^ index * term index) -
          (∑ index ∈ Finset.range (2 * iterations),
            (-1 : ℝ) ^ index * term index) = term (2 * iterations) := by
      rw [Finset.sum_range_succ]
      simp [term]
    simpa [term] using (show
      (∑ index ∈ Finset.range (2 * iterations + 1),
          (-1 : ℝ) ^ index * term index) - Real.arctan x ≤
          term (2 * iterations) from by
        calc
          _ ≤ (∑ index ∈ Finset.range (2 * iterations + 1),
                (-1 : ℝ) ^ index * term index) -
              (∑ index ∈ Finset.range (2 * iterations),
                (-1 : ℝ) ^ index * term index) := by linarith
          _ = term (2 * iterations) := difference)

theorem piApproximation_error (workingBits : Nat) :
    |(piApproximation workingBits : ℝ) - Real.pi| ≤
      (piError workingBits : ℝ) := by
  let iterations := arctangentIterations workingBits
  have terms : arctangentTerms workingBits = 2 * iterations + 1 := by
    simp [arctangentTerms, iterations]
  have five := atanSeries_odd_error (1 / 5) (by norm_num) (by norm_num)
    iterations
  have twoThirtyNine := atanSeries_odd_error (1 / 239)
    (by norm_num) (by norm_num) iterations
  have machin : Real.pi =
      4 * (4 * Real.arctan (1 / 5) - Real.arctan (1 / 239)) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num [div_eq_mul_inv]
    nlinarith [h]
  rw [machin]
  rw [piApproximation, piError, terms]
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [abs_le]
  constructor <;> nlinarith [five.1, five.2,
    twoThirtyNine.1, twoThirtyNine.2]

theorem piError_nonnegative (workingBits : Nat) :
    0 ≤ (piError workingBits : ℝ) := by
  simp only [piError]
  positivity

theorem piError_le_one (workingBits : Nat) :
    (piError workingBits : ℝ) ≤ 1 := by
  let last := arctangentTerms workingBits - 1
  have lastValue : last = 2 * arctangentIterations workingBits := by
    simp [last, arctangentTerms]
  have iterationsLower : 2 ≤ arctangentIterations workingBits := by
    simp [arctangentIterations]
  have exponentOrder : 5 ≤ 2 * last + 1 := by omega
  have fivePower :
      ((1 / 5 : ℝ) ^ (2 * last + 1)) ≤ (1 / 5 : ℝ) ^ 5 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) exponentOrder
  have twoThirtyNinePower :
      ((1 / 239 : ℝ) ^ (2 * last + 1)) ≤ (1 / 239 : ℝ) ^ 5 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) exponentOrder
  have denominator : (1 : ℝ) ≤ 2 * last + 1 := by
    exact_mod_cast (show 1 ≤ 2 * last + 1 by omega)
  have fiveTerm :
      (1 / 5 : ℝ) ^ (2 * last + 1) / (2 * last + 1) ≤
        (1 / 5 : ℝ) ^ 5 := by
    calc
      _ ≤ (1 / 5 : ℝ) ^ (2 * last + 1) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * last + 1)).2
        nlinarith [show 0 ≤ (1 / 5 : ℝ) ^ (2 * last + 1) by positivity]
      _ ≤ _ := fivePower
  have twoThirtyNineTerm :
      (1 / 239 : ℝ) ^ (2 * last + 1) / (2 * last + 1) ≤
        (1 / 239 : ℝ) ^ 5 := by
    calc
      _ ≤ (1 / 239 : ℝ) ^ (2 * last + 1) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * last + 1)).2
        nlinarith [show 0 ≤ (1 / 239 : ℝ) ^ (2 * last + 1) by positivity]
      _ ≤ _ := twoThirtyNinePower
  rw [piError]
  change (4 * (4 * ((1 / 5 : Rat) ^ (2 * last + 1) /
      (2 * last + 1)) + (1 / 239 : Rat) ^ (2 * last + 1) /
      (2 * last + 1)) : Rat) ≤ (1 : ℝ)
  push_cast
  norm_num at fiveTerm twoThirtyNineTerm ⊢
  nlinarith

theorem approximateAngle_error (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    |(approximateAngle workingBits stage offset : ℝ) -
        (-(Real.pi * offset.val / (2 ^ stage.val)))| ≤
      (piError workingBits : ℝ) := by
  have denominatorPositive : (0 : ℝ) < 2 ^ stage.val := by positivity
  have ratioNonnegative :
      (0 : ℝ) ≤ (offset.val : ℝ) / (2 ^ stage.val) := by positivity
  have ratioLeOne :
      (offset.val : ℝ) / (2 ^ stage.val) ≤ 1 := by
    apply (div_le_one denominatorPositive).2
    exact_mod_cast offset.isLt.le
  rw [approximateAngle]
  push_cast
  rw [show -(↑(piApproximation workingBits) * ↑offset.val / 2 ^ stage.val) -
      -(Real.pi * ↑offset.val / 2 ^ stage.val) =
      -(↑(piApproximation workingBits) - Real.pi) *
        (↑offset.val / 2 ^ stage.val) by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg ratioNonnegative]
  calc
    |↑(piApproximation workingBits) - Real.pi| *
          (↑offset.val / 2 ^ stage.val) ≤
        (piError workingBits : ℝ) * 1 := by
      exact mul_le_mul (piApproximation_error workingBits) ratioLeOne
        ratioNonnegative (piError_nonnegative workingBits)
    _ = _ := by ring

theorem approximateAngle_abs_le_five (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    |(approximateAngle workingBits stage offset : ℝ)| ≤ 5 := by
  let exactAngle : ℝ := -(Real.pi * offset.val / (2 ^ stage.val))
  have denominatorPositive : (0 : ℝ) < 2 ^ stage.val := by positivity
  have ratioNonnegative :
      (0 : ℝ) ≤ (offset.val : ℝ) / (2 ^ stage.val) := by positivity
  have ratioLeOne :
      (offset.val : ℝ) / (2 ^ stage.val) ≤ 1 := by
    apply (div_le_one denominatorPositive).2
    exact_mod_cast offset.isLt.le
  have exactAngleBound : |exactAngle| ≤ Real.pi := by
    dsimp [exactAngle]
    rw [show Real.pi * (offset.val : ℝ) / (2 ^ stage.val) =
      Real.pi * ((offset.val : ℝ) / (2 ^ stage.val)) by ring]
    rw [abs_neg, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg ratioNonnegative]
    nlinarith [Real.pi_pos]
  have approximationBound :
      |(approximateAngle workingBits stage offset : ℝ) - exactAngle| ≤ 1 :=
    (approximateAngle_error workingBits stage offset).trans
      (piError_le_one workingBits)
  calc
    |(approximateAngle workingBits stage offset : ℝ)| =
        |((approximateAngle workingBits stage offset : ℝ) - exactAngle) +
          exactAngle| := by ring_nf
    _ ≤ |(approximateAngle workingBits stage offset : ℝ) - exactAngle| +
        |exactAngle| := abs_add_le _ _
    _ ≤ 1 + Real.pi := add_le_add approximationBound exactAngleBound
    _ ≤ 5 := by linarith [Real.pi_le_four]

private theorem exp_I_lipschitz (first second : ℝ) :
    ‖Complex.exp ((first : ℂ) * Complex.I) -
        Complex.exp ((second : ℂ) * Complex.I)‖ ≤ |first - second| := by
  have factorization :
      Complex.exp ((first : ℂ) * Complex.I) -
          Complex.exp ((second : ℂ) * Complex.I) =
        Complex.exp ((second : ℂ) * Complex.I) *
          (Complex.exp (((first - second : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [factorization, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Real.exp_zero,
    one_mul]
  simpa [mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := first - second))

@[simp] private theorem rationalI_cast :
    rationalComplexToComplex rationalI = Complex.I := by
  apply Complex.ext <;> simp [rationalI, rationalComplexToComplex]

@[simp] private theorem iPower_cast (power : Nat) :
    rationalComplexToComplex (iPower power) = Complex.I ^ power := by
  induction power with
  | zero => simp [iPower, rationalComplexToComplex]
  | succ power induction => simp [iPower, induction, pow_succ]

@[simp] private theorem scale_cast (factor : Rat)
    (value : HTFFT.Complex Rat) :
    rationalComplexToComplex (scale factor value) =
      (factor : ℂ) * rationalComplexToComplex value := by
  apply Complex.ext <;> simp [scale, rationalComplexToComplex]

theorem expSeries_cast (angle : Rat) (terms : Nat) :
    rationalComplexToComplex (expSeries angle terms) =
      ∑ term ∈ Finset.range terms,
        (((angle : ℝ) : ℂ) * Complex.I) ^ term / term.factorial := by
  induction terms with
  | zero => simp [expSeries, rationalComplexToComplex]
  | succ terms induction =>
      rw [expSeries, rationalComplexToComplex_add, induction,
        Finset.sum_range_succ]
      simp only [scale_cast, iPower_cast]
      push_cast
      rw [mul_pow]
      ring

theorem expSeries_error (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    ‖rationalComplexToComplex
          (expSeries (approximateAngle workingBits stage offset)
            (exponentialTerms workingBits)) -
        Complex.exp
          (((approximateAngle workingBits stage offset : ℝ) : ℂ) *
            Complex.I)‖ ≤
      (2 * 5 ^ exponentialTerms workingBits /
        (exponentialTerms workingBits).factorial : Rat) := by
  let angle := approximateAngle workingBits stage offset
  let terms := exponentialTerms workingBits
  have angleBound : |(angle : ℝ)| ≤ 5 :=
    approximateAngle_abs_le_five workingBits stage offset
  have termsValue : terms = workingBits + 13 := by
    simp [terms, exponentialTerms]
  have ratioBound :
      ‖((angle : ℝ) : ℂ) * Complex.I‖ / terms.succ ≤ (1 : ℝ) / 2 := by
    rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs]
    have termsLower : (10 : ℝ) ≤ terms.succ := by
      exact_mod_cast (show 10 ≤ terms.succ by omega)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < terms.succ)).2
    nlinarith
  have seriesBound := Complex.exp_bound'
    (x := ((angle : ℝ) : ℂ) * Complex.I) (n := terms) ratioBound
  rw [expSeries_cast]
  rw [norm_sub_rev]
  calc
    ‖Complex.exp (((angle : ℝ) : ℂ) * Complex.I) -
        ∑ term ∈ Finset.range terms,
          (((angle : ℝ) : ℂ) * Complex.I) ^ term / term.factorial‖ ≤
        ‖((angle : ℝ) : ℂ) * Complex.I‖ ^ terms /
          terms.factorial * 2 := seriesBound
    _ ≤ 5 ^ terms / terms.factorial * 2 := by
      gcongr
      simpa [Complex.norm_mul, Real.norm_eq_abs] using angleBound
    _ = (2 * 5 ^ exponentialTerms workingBits /
        (exponentialTerms workingBits).factorial : Rat) := by
      subst terms
      push_cast
      ring

theorem exactTwiddle_eq_exp (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    exactTwiddle stage offset =
      Complex.exp (((-(Real.pi * offset.val / (2 ^ stage.val)) : ℝ) : ℂ) *
        Complex.I) := by
  rw [exactTwiddle, Exact.twiddle_eq_fourierCoefficient,
    Exact.fourierCoefficient_eq_exp, Exact.halfIndexEquiv_left_val]
  rw [show stage.val + 1 = stage.val.succ by omega, pow_succ]
  push_cast
  field_simp [pow_ne_zero]

theorem approximationError_nonnegative (workingBits : Nat) :
    0 ≤ (approximationError workingBits : ℝ) := by
  simp only [approximationError]
  push_cast
  positivity [piError_nonnegative workingBits]

private theorem exponential_factorial_bound (workingBits : Nat) :
    2 ^ (workingBits + 2) * 5 ^ (workingBits + 13) ≤
      (workingBits + 13).factorial := by
  induction workingBits with
  | zero => norm_num [Nat.factorial]
  | succ workingBits induction =>
      calc
        2 ^ (workingBits + 1 + 2) * 5 ^ (workingBits + 1 + 13) =
            10 * (2 ^ (workingBits + 2) * 5 ^ (workingBits + 13)) := by
          ring
        _ ≤ 10 * (workingBits + 13).factorial :=
          Nat.mul_le_mul_left 10 induction
        _ ≤ (workingBits + 14) * (workingBits + 13).factorial := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = (workingBits + 1 + 13).factorial := by
          rw [show workingBits + 1 + 13 = (workingBits + 13) + 1 by omega]
          exact (Nat.factorial_succ (workingBits + 13)).symm

private theorem exponentialError_le_half_precision (workingBits : Nat) :
    (2 * 5 ^ exponentialTerms workingBits /
        (exponentialTerms workingBits).factorial : Rat) ≤
      1 / (2 : Rat) ^ (workingBits + 1) := by
  rw [exponentialTerms]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have bound := exponential_factorial_bound workingBits
  have naturalBound :
    2 * 5 ^ (workingBits + 13) * 2 ^ (workingBits + 1) ≤
      (workingBits + 13).factorial := by
    calc
      _ = 2 ^ (workingBits + 2) * 5 ^ (workingBits + 13) := by ring
      _ ≤ _ := bound
  have rationalBound :
      (2 * 5 ^ (workingBits + 13) * 2 ^ (workingBits + 1) : Rat) ≤
        (workingBits + 13).factorial := by
    exact_mod_cast naturalBound
  simpa using rationalBound

private theorem pi_power_bound_for_quotient (quotient : Nat) :
    20 * 2 ^ (8 * (quotient + 1)) ≤ 5 ^ (4 * quotient + 9) := by
  induction quotient with
  | zero => norm_num
  | succ quotient induction =>
      calc
        20 * 2 ^ (8 * (quotient + 1 + 1)) =
            256 * (20 * 2 ^ (8 * (quotient + 1))) := by ring
        _ ≤ 256 * 5 ^ (4 * quotient + 9) :=
          Nat.mul_le_mul_left 256 induction
        _ ≤ 625 * 5 ^ (4 * quotient + 9) := by
          exact Nat.mul_le_mul_right _ (by norm_num)
        _ = 5 ^ (4 * (quotient + 1) + 9) := by ring

private theorem pi_natural_power_bound (workingBits : Nat) :
    20 * 2 ^ (workingBits + 1) ≤
      5 ^ (4 * arctangentIterations workingBits + 1) := by
  let quotient := workingBits / 8
  have exponentOrder : workingBits + 1 ≤ 8 * (quotient + 1) := by
    dsimp [quotient]
    omega
  have powerOrder :
      2 ^ (workingBits + 1) ≤ 2 ^ (8 * (quotient + 1)) := by
    exact pow_le_pow_right' (by norm_num) exponentOrder
  calc
    20 * 2 ^ (workingBits + 1) ≤
        20 * 2 ^ (8 * (quotient + 1)) := Nat.mul_le_mul_left 20 powerOrder
    _ ≤ 5 ^ (4 * quotient + 9) := pi_power_bound_for_quotient quotient
    _ = 5 ^ (4 * arctangentIterations workingBits + 1) := by
      have iterations : arctangentIterations workingBits = quotient + 2 := by
        simp [arctangentIterations, quotient]
      rw [iterations]
      congr 1

private theorem piError_le_half_precision (workingBits : Nat) :
    piError workingBits ≤ 1 / (2 : Rat) ^ (workingBits + 1) := by
  let last := arctangentTerms workingBits - 1
  let exponent := 2 * last + 1
  have lastValue : last = 2 * arctangentIterations workingBits := by
    simp [last, arctangentTerms]
  have exponentValue :
      exponent = 4 * arctangentIterations workingBits + 1 := by
    simp [exponent, lastValue]
    ring
  have denominatorPositive : (0 : Rat) < 2 * last + 1 := by positivity
  have denominatorOne : (1 : Rat) ≤ 2 * last + 1 := by
    exact_mod_cast (show 1 ≤ 2 * last + 1 by omega)
  have fiveNonnegative : (0 : Rat) ≤ (1 / 5) ^ exponent := by positivity
  have fiveTerm :
      (1 / 5 : Rat) ^ exponent / (2 * last + 1) ≤
        (1 / 5 : Rat) ^ exponent := by
    apply (div_le_iff₀ denominatorPositive).2
    nlinarith
  have smallerPower :
      (1 / 239 : Rat) ^ exponent ≤ (1 / 5 : Rat) ^ exponent := by
    gcongr
    norm_num
  have twoThirtyNineTerm :
      (1 / 239 : Rat) ^ exponent / (2 * last + 1) ≤
        (1 / 5 : Rat) ^ exponent := by
    calc
      _ ≤ (1 / 239 : Rat) ^ exponent := by
        apply (div_le_iff₀ denominatorPositive).2
        nlinarith [show (0 : Rat) ≤ (1 / 239) ^ exponent by positivity]
      _ ≤ _ := smallerPower
  have coarse : piError workingBits ≤ 20 * (1 / 5 : Rat) ^ exponent := by
    rw [piError]
    change 4 * (4 * ((1 / 5 : Rat) ^ exponent / (2 * last + 1)) +
      (1 / 239 : Rat) ^ exponent / (2 * last + 1)) ≤ _
    nlinarith
  apply coarse.trans
  rw [exponentValue]
  rw [one_div, inv_pow]
  change 20 / (5 : Rat) ^ (4 * arctangentIterations workingBits + 1) ≤
    1 / (2 : Rat) ^ (workingBits + 1)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have naturalBound := pi_natural_power_bound workingBits
  have rationalBound :
      (20 * 2 ^ (workingBits + 1) : Rat) ≤
        5 ^ (4 * arctangentIterations workingBits + 1) := by
    exact_mod_cast naturalBound
  simpa using rationalBound

/-- The term-selection policy meets every requested binary working
precision. This is the generic guarantee used by all generated tables. -/
theorem precisionSufficient (workingBits : Nat) :
    PrecisionSufficient workingBits := by
  rw [PrecisionSufficient, approximationError]
  calc
    piError workingBits +
        2 * 5 ^ exponentialTerms workingBits /
          (exponentialTerms workingBits).factorial ≤
      1 / (2 : Rat) ^ (workingBits + 1) +
        1 / (2 : Rat) ^ (workingBits + 1) :=
      add_le_add (piError_le_half_precision workingBits)
        (exponentialError_le_half_precision workingBits)
    _ = 1 / (2 : Rat) ^ workingBits := by
      rw [pow_succ]
      field_simp
      ring

theorem approximationError_le_workingQuantum (workingBits : Nat) :
    (approximationError workingBits : ℝ) ≤
      1 / (2 : ℝ) ^ workingBits := by
  have rational := precisionSufficient workingBits
  unfold PrecisionSufficient at rational
  have casted :
      (approximationError workingBits : ℝ) ≤
        ((1 / (2 : Rat) ^ workingBits : Rat) : ℝ) :=
    Rat.cast_le.2 rational
  simpa using casted

theorem value_error (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    ‖rationalComplexToComplex (value workingBits stage offset) -
        exactTwiddle stage offset‖ ≤
      (approximationError workingBits : ℝ) := by
  let approximate := (approximateAngle workingBits stage offset : ℝ)
  let exact := -(Real.pi * offset.val / (2 ^ stage.val))
  have series := expSeries_error workingBits stage offset
  have angle := approximateAngle_error workingBits stage offset
  have exponential :
      ‖Complex.exp ((approximate : ℂ) * Complex.I) -
          Complex.exp ((exact : ℂ) * Complex.I)‖ ≤
        (piError workingBits : ℝ) :=
    (exp_I_lipschitz approximate exact).trans (by simpa [approximate, exact] using angle)
  rw [value, exactTwiddle_eq_exp]
  change ‖rationalComplexToComplex
      (expSeries (approximateAngle workingBits stage offset)
        (exponentialTerms workingBits)) -
      Complex.exp ((exact : ℂ) * Complex.I)‖ ≤ _
  calc
    _ ≤ ‖rationalComplexToComplex
            (expSeries (approximateAngle workingBits stage offset)
              (exponentialTerms workingBits)) -
          Complex.exp ((approximate : ℂ) * Complex.I)‖ +
        ‖Complex.exp ((approximate : ℂ) * Complex.I) -
          Complex.exp ((exact : ℂ) * Complex.I)‖ := norm_sub_triangle _ _ _
    _ ≤ (2 * 5 ^ exponentialTerms workingBits /
          (exponentialTerms workingBits).factorial : Rat) +
        (piError workingBits : ℝ) := by
      apply add_le_add
      · simpa [approximate] using series
      · exact exponential
    _ = (approximationError workingBits : ℝ) := by
      rw [approximationError]
      push_cast
      ring

theorem approximations_enclosure (depth : Nat)
    (workingPrecision : Fin depth → Nat) :
    TwiddleEnclosure (approximations depth workingPrecision)
      (fun stage => (approximationError (workingPrecision stage) : ℝ)) := by
  refine
    { error_nonnegative := fun stage =>
        approximationError_nonnegative (workingPrecision stage)
      real_lower := ?_
      real_upper := ?_
      imag_lower := ?_
      imag_upper := ?_ }
  · intro stage offset
    have bound := (Complex.abs_re_le_norm _).trans
      (value_error (workingPrecision stage) stage offset)
    rw [abs_le] at bound
    simpa [approximations, Complex.sub_re, rationalComplexToComplex_re,
      add_comm] using bound.2
  · intro stage offset
    have bound := (Complex.abs_re_le_norm _).trans
      (value_error (workingPrecision stage) stage offset)
    rw [abs_le] at bound
    simpa [approximations, Complex.sub_re, rationalComplexToComplex_re] using bound.1
  · intro stage offset
    have bound := (Complex.abs_im_le_norm _).trans
      (value_error (workingPrecision stage) stage offset)
    rw [abs_le] at bound
    simpa [approximations, Complex.sub_im, rationalComplexToComplex_im,
      add_comm] using bound.2
  · intro stage offset
    have bound := (Complex.abs_im_le_norm _).trans
      (value_error (workingPrecision stage) stage offset)
    rw [abs_le] at bound
    simpa [approximations, Complex.sub_im, rationalComplexToComplex_im] using bound.1

theorem forFormats_enclosure (formats : Fin depth → Format)
    (guardBits : Nat) :
    TwiddleEnclosure (forFormats formats guardBits)
      (fun stage =>
        (approximationError (workingBits formats guardBits stage) : ℝ)) := by
  exact approximations_enclosure depth (workingBits formats guardBits)

/-- The signed Q2 format used for generated roots of unity. -/
def q2Format (fractionalBits : Nat) : Format :=
  ⟨fractionalBits + 2, fractionalBits⟩

private theorem value_norm_le (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    ‖rationalComplexToComplex (value workingBits stage offset)‖ ≤
      1 + (approximationError workingBits : ℝ) := by
  let approximate := rationalComplexToComplex (value workingBits stage offset)
  let exact := exactTwiddle stage offset
  calc
    ‖approximate‖ = ‖(approximate - exact) + exact‖ := by
      congr 1
      ring
    _ ≤ ‖approximate - exact‖ + ‖exact‖ := norm_add_le _ _
    _ ≤ (approximationError workingBits : ℝ) + 1 := by
      exact add_le_add (value_error workingBits stage offset)
        (le_of_eq (norm_exactTwiddle stage offset))
    _ = _ := by ring

theorem value_real_abs_le (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    |((value workingBits stage offset).real : ℝ)| ≤
      1 + (approximationError workingBits : ℝ) := by
  simpa [rationalComplexToComplex_re] using
    (Complex.abs_re_le_norm
      (rationalComplexToComplex (value workingBits stage offset))).trans
        (value_norm_le workingBits stage offset)

theorem value_imag_abs_le (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    |((value workingBits stage offset).imag : ℝ)| ≤
      1 + (approximationError workingBits : ℝ) := by
  simpa [rationalComplexToComplex_im] using
    (Complex.abs_im_le_norm
      (rationalComplexToComplex (value workingBits stage offset))).trans
        (value_norm_le workingBits stage offset)

private theorem approximationError_le_guardedQuantum
    (fractionalBits guardBits : Nat) (guardBits_pos : 0 < guardBits) :
    (approximationError (fractionalBits + guardBits) : ℝ) ≤
      1 / (2 : ℝ) ^ (fractionalBits + 1) := by
  apply (approximationError_le_workingQuantum _).trans
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Precision-generated roots of unity always fit signed Q2 storage after
nearest-even quantization. This eliminates table-by-table range proofs. -/
theorem generated_q2_fits
    (fractionalBits : Fin depth → Nat)
    (fractionalBits_min : ∀ stage, 2 ≤ fractionalBits stage)
    (guardBits : Nat) (guardBits_pos : 0 < guardBits) :
    QuantizedTwiddleFits
      (fun stage => q2Format (fractionalBits stage))
      (fun _ => .nearestTiesToEven)
      (forFormats (fun stage => q2Format (fractionalBits stage)) guardBits) := by
  intro stage offset
  constructor
  · apply encode_nearest_fits_q2 _ (fractionalBits_min stage)
    apply (value_real_abs_le _ stage offset).trans
    change 1 + (approximationError
      (fractionalBits stage + guardBits) : ℝ) ≤ _
    simpa [add_comm] using add_le_add_left
      (approximationError_le_guardedQuantum
        (fractionalBits stage) guardBits guardBits_pos) 1
  · apply encode_nearest_fits_q2 _ (fractionalBits_min stage)
    apply (value_imag_abs_le _ stage offset).trans
    change 1 + (approximationError
      (fractionalBits stage + guardBits) : ℝ) ≤ _
    simpa [add_comm] using add_le_add_left
      (approximationError_le_guardedQuantum
        (fractionalBits stage) guardBits guardBits_pos) 1

end HTFFT.Fixed.TwiddleGenerator
