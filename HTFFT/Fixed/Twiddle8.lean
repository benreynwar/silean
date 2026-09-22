import HTFFT.Fixed.TwiddleTable
import Mathlib.Tactic

namespace HTFFT.Fixed.Twiddle8

open HTFFT
open HTFFT.FixedPoint

/-- Q2.8 twiddles: one sign bit, one integer bit, and eight fractional bits. -/
def twiddleFormat : Format := ⟨10, 8⟩

/-- A representative data configuration for an eight-point transform. Only
its twiddle format is relevant to this file. -/
def config : Config 3 where
  boundaryFormat boundary := ⟨12 + boundary.val, 8⟩
  twiddleFormat _ := twiddleFormat
  productFormat stage := ⟨12 + stage.val, 8⟩
  rounding _ := .nearestTiesToEven

/-- Twiddle-table quantization is explicit and independent of the butterfly's
arithmetic-rounding choice. -/
def rounding : Fin 3 → RoundingMode := fun _ => .nearestTiesToEven

/-- The dyadic approximation `181 / 256` to `sqrt 2 / 2`. -/
def diagonal : Rat := 181 / 256

/-- Rational centers for all twiddles used by an eight-point radix-two FFT. -/
def approximations : RationalTwiddleTable 3 where
  value stage offset :=
    match stage.val, offset.val with
    | 0, _ => ⟨1, 0⟩
    | 1, 0 => ⟨1, 0⟩
    | 1, _ => ⟨0, -1⟩
    | 2, 0 => ⟨1, 0⟩
    | 2, 1 => ⟨diagonal, -diagonal⟩
    | 2, 2 => ⟨0, -1⟩
    | 2, _ => ⟨-diagonal, -diagonal⟩
    | _, _ => ⟨0, 0⟩

/-- Component radius of the rational enclosure. It is exact in stages zero
and one; final-stage diagonal entries use one Q2.8 LSB. -/
noncomputable def componentApproximationError (stage : Fin 3) : ℝ :=
  match stage.val with
  | 0 => 0
  | 1 => 0
  | _ => 1 / 256

/-- Euclidean complex error certified for the stored twiddles. -/
noncomputable def twiddleError (stage : Fin 3) : ℝ :=
  Real.sqrt 2 * componentApproximationError stage

/-- The generated raw integer table. -/
def table : TwiddleTable 3 :=
  quantizeTwiddleTable config.twiddleFormat rounding approximations

theorem diagonal_lower :
    (181 / 256 : ℝ) ≤ Real.sqrt 2 / 2 := by
  have sqrtNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrtSquared : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have lowerSquared : (181 / 128 : ℝ) ^ 2 ≤ 2 := by
    norm_num
  nlinarith

theorem diagonal_upper :
    Real.sqrt 2 / 2 ≤ (182 / 256 : ℝ) := by
  have sqrtNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrtSquared : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have upperNonnegative : (0 : ℝ) ≤ 91 / 64 := by
    norm_num
  have upperSquared : (2 : ℝ) ≤ (91 / 64) ^ 2 := by
    norm_num
  nlinarith

theorem exp_neg_pi_div_four_mul_I :
    Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) -
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  ring

theorem exact_stage1_one :
    exactTwiddle (depth := 3) (1 : Fin 3)
        (1 : Fin (2 ^ (1 : Fin 3).val)) =
      -Complex.I := by
  rw [exactTwiddle]
  change ZMod.stdAddChar (-(1 : ZMod 4)) = -Complex.I
  rw [show -(1 : ZMod 4) = ((-1 : Int) : ZMod 4) by norm_num,
    ZMod.stdAddChar_coe, ← Complex.exp_neg_pi_div_two_mul_I]
  congr 1
  push_cast
  ring_nf

theorem exact_stage2_one :
    exactTwiddle (depth := 3) (2 : Fin 3)
        (1 : Fin (2 ^ (2 : Fin 3).val)) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) -
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [exactTwiddle]
  change ZMod.stdAddChar (-(1 : ZMod 8)) = _
  rw [show -(1 : ZMod 8) = ((-1 : Int) : ZMod 8) by norm_num,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf
  rw [show (Real.pi : ℂ) * Complex.I * (-1 / 4) =
      ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring_nf,
    exp_neg_pi_div_four_mul_I]
  push_cast
  ring

theorem exact_stage2_two :
    exactTwiddle (depth := 3) (2 : Fin 3)
        (2 : Fin (2 ^ (2 : Fin 3).val)) =
      -Complex.I := by
  rw [exactTwiddle]
  change ZMod.stdAddChar (-(2 : ZMod 8)) = -Complex.I
  rw [show -(2 : ZMod 8) = ((-2 : Int) : ZMod 8) by norm_num,
    ZMod.stdAddChar_coe, ← Complex.exp_neg_pi_div_two_mul_I]
  congr 1
  push_cast
  ring_nf

theorem exact_stage2_three :
    exactTwiddle (depth := 3) (2 : Fin 3)
        (3 : Fin (2 ^ (2 : Fin 3).val)) =
      -((Real.sqrt 2 / 2 : ℝ) : ℂ) -
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [exactTwiddle]
  change ZMod.stdAddChar (-(3 : ZMod 8)) = _
  rw [show -(3 : ZMod 8) = ((-3 : Int) : ZMod 8) by norm_num,
    ZMod.stdAddChar_coe]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (-3) / 8 =
      ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I +
        ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring_nf,
    Complex.exp_add]
  have half :
      Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
        -Complex.I := by
    rw [← Complex.exp_neg_pi_div_two_mul_I]
    congr 1
    push_cast
    ring_nf
  rw [half, exp_neg_pi_div_four_mul_I]
  push_cast
  ring_nf
  simp
  ring

private theorem exact_stage1_one_of_values (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) (stageValue : stage.val = 1)
    (offsetValue : offset.val = 1) :
    exactTwiddle stage offset = -Complex.I := by
  have stageEq : stage = (1 : Fin 3) := by
    apply Fin.ext
    exact stageValue
  subst stage
  have offsetEq : offset = (1 : Fin (2 ^ (1 : Fin 3).val)) := by
    apply Fin.ext
    exact offsetValue
  subst offset
  exact exact_stage1_one

private theorem exact_stage2_one_of_values (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) (stageValue : stage.val = 2)
    (offsetValue : offset.val = 1) :
    exactTwiddle stage offset =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) -
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have stageEq : stage = (2 : Fin 3) := by
    apply Fin.ext
    exact stageValue
  subst stage
  have offsetEq : offset = (1 : Fin (2 ^ (2 : Fin 3).val)) := by
    apply Fin.ext
    exact offsetValue
  subst offset
  exact exact_stage2_one

private theorem exact_stage2_two_of_values (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) (stageValue : stage.val = 2)
    (offsetValue : offset.val = 2) :
    exactTwiddle stage offset = -Complex.I := by
  have stageEq : stage = (2 : Fin 3) := by
    apply Fin.ext
    exact stageValue
  subst stage
  have offsetEq : offset = (2 : Fin (2 ^ (2 : Fin 3).val)) := by
    apply Fin.ext
    exact offsetValue
  subst offset
  exact exact_stage2_two

private theorem exact_stage2_three_of_values (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) (stageValue : stage.val = 2)
    (offsetValue : offset.val = 3) :
    exactTwiddle stage offset =
      -((Real.sqrt 2 / 2 : ℝ) : ℂ) -
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have stageEq : stage = (2 : Fin 3) := by
    apply Fin.ext
    exact stageValue
  subst stage
  have offsetEq : offset = (3 : Fin (2 ^ (2 : Fin 3).val)) := by
    apply Fin.ext
    exact offsetValue
  subst offset
  exact exact_stage2_three

theorem enclosure :
    TwiddleEnclosure approximations componentApproximationError := by
  refine
    { error_nonnegative := ?_
      real_lower := ?_
      real_upper := ?_
      imag_lower := ?_
      imag_upper := ?_ }
  · intro stage
    fin_cases stage <;> norm_num [componentApproximationError]
  · intro stage offset
    fin_cases stage <;> fin_cases offset
    all_goals first
      | rw [exactTwiddle_of_offset_val_zero _ _ rfl]
      | rw [exact_stage1_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_two_of_values _ _ rfl rfl]
      | rw [exact_stage2_three_of_values _ _ rfl rfl]
    all_goals
      norm_num [approximations, componentApproximationError, diagonal,
        Rat.cast_divInt] <;>
        linarith [diagonal_lower, diagonal_upper]
  · intro stage offset
    fin_cases stage <;> fin_cases offset
    all_goals first
      | rw [exactTwiddle_of_offset_val_zero _ _ rfl]
      | rw [exact_stage1_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_two_of_values _ _ rfl rfl]
      | rw [exact_stage2_three_of_values _ _ rfl rfl]
    all_goals
      norm_num [approximations, componentApproximationError, diagonal,
        Rat.cast_divInt] <;>
        linarith [diagonal_lower, diagonal_upper]
  · intro stage offset
    fin_cases stage <;> fin_cases offset
    all_goals first
      | rw [exactTwiddle_of_offset_val_zero _ _ rfl]
      | rw [exact_stage1_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_two_of_values _ _ rfl rfl]
      | rw [exact_stage2_three_of_values _ _ rfl rfl]
    all_goals
      norm_num [approximations, componentApproximationError, diagonal,
        Rat.cast_divInt] <;>
        linarith [diagonal_lower, diagonal_upper]
  · intro stage offset
    fin_cases stage <;> fin_cases offset
    all_goals first
      | rw [exactTwiddle_of_offset_val_zero _ _ rfl]
      | rw [exact_stage1_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_one_of_values _ _ rfl rfl]
      | rw [exact_stage2_two_of_values _ _ rfl rfl]
      | rw [exact_stage2_three_of_values _ _ rfl rfl]
    all_goals
      norm_num [approximations, componentApproximationError, diagonal,
        Rat.cast_divInt] <;>
        linarith [diagonal_lower, diagonal_upper]

theorem table_fits :
    QuantizedTwiddleFits config.twiddleFormat rounding approximations := by
  intro stage offset
  fin_cases stage <;> fin_cases offset <;>
    norm_num [config, twiddleFormat, quantizeTwiddleTable, approximations,
      rounding, diagonal, FixedPoint.encodeComplex, HTFFT.Complex.map,
      FixedPoint.encode, FixedPoint.roundRatio, ComplexFits, Fits, FitsWidth,
      signedMin, signedMax, Format.scale]

theorem table_decodes_to_approximations (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) :
    decodeTwiddle config table stage offset =
      rationalComplexToComplex (approximations.value stage offset) := by
  fin_cases stage <;> fin_cases offset <;>
    norm_num [decodeTwiddle, table, config, twiddleFormat,
      quantizeTwiddleTable, approximations, rounding, diagonal, decodeComplex,
      rationalComplexToComplex, FixedPoint.decodeComplex,
      FixedPoint.encodeComplex, HTFFT.Complex.map, FixedPoint.decode,
      FixedPoint.encode, FixedPoint.roundRatio, Format.scale, Rat.cast_divInt]

/-- The generated Q2.8 table has exact stage-zero and stage-one entries. Its
only approximation error is the certified `1 / 256` enclosure of the two
diagonal components in the final stage. -/
theorem accuracy : TwiddleAccuracy config table twiddleError := by
  refine
    { error_nonnegative := fun stage =>
        mul_nonneg (Real.sqrt_nonneg _)
          (enclosure.error_nonnegative stage)
      fits := ?_
      accurate := ?_ }
  · exact table_fits
  · intro stage offset
    rw [table_decodes_to_approximations]
    exact enclosure.normWithin stage offset

end HTFFT.Fixed.Twiddle8
