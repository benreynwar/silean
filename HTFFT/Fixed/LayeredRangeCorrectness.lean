import HTFFT.Fixed.LayeredCorrectness
import HTFFT.Fixed.LayeredRange

namespace HTFFT.Fixed

/-- Componentwise ordering for the magnitude/error pair used by range
certificates. -/
def Bounds.LE (left right : Bounds) : Prop :=
  left.magnitude ≤ right.magnitude ∧ left.error ≤ right.error

/-- The bounds recurrence is monotone in both its incoming bounds and its
twiddle-error allowance. -/
theorem advanceBounds_mono (config : Config depth) (stage : Fin depth)
    (left right : Bounds) (leftError rightError : Fin depth → ℝ)
    (leftNonnegative : left.Nonnegative)
    (rightNonnegative : right.Nonnegative)
    (leftErrorNonnegative : 0 ≤ leftError stage)
    (errorOrdered : leftError stage ≤ rightError stage)
    (boundsOrdered : left.LE right) :
    (advanceBounds config leftError stage left).LE
      (advanceBounds config rightError stage right) := by
  constructor
  · simp only [advanceBounds]
    exact mul_le_mul_of_nonneg_left boundsOrdered.1 (by norm_num)
  · simp only [advanceBounds]
    have rightErrorNonnegative := leftErrorNonnegative.trans errorOrdered
    have coefficientOrdered :
        2 + leftError stage ≤ 2 + rightError stage := by linarith
    have first := mul_le_mul coefficientOrdered boundsOrdered.2
      leftNonnegative.2 (by positivity)
    have second := mul_le_mul boundsOrdered.1 errorOrdered
      leftErrorNonnegative rightNonnegative.1
    linarith

/-- Pointwise enlargement of the twiddle-error budget enlarges every
propagated boundary bound. -/
theorem boundsAt_mono_twiddleError (config : Config depth)
    (leftError rightError : Fin depth → ℝ) (initial : Bounds)
    (initialNonnegative : initial.Nonnegative)
    (leftNonnegative : ∀ stage, 0 ≤ leftError stage)
    (rightNonnegative : ∀ stage, 0 ≤ rightError stage)
    (ordered : ∀ stage, leftError stage ≤ rightError stage)
    (boundary : Exact.LayerBoundary depth) :
    (boundsAt config leftError initial boundary).LE
      (boundsAt config rightError initial boundary) := by
  induction boundary using Fin.induction with
  | zero =>
      exact ⟨le_rfl, le_rfl⟩
  | succ stage inductionHypothesis =>
      rw [boundsAt_boundarySucc, boundsAt_boundarySucc]
      have leftBoundsNonnegative := boundsAt_nonnegative config leftError
        initial initialNonnegative leftNonnegative stage.castSucc
      have rightBoundsNonnegative := boundsAt_nonnegative config rightError
        initial initialNonnegative rightNonnegative stage.castSucc
      simpa only using advanceBounds_mono config stage _ _
        leftError rightError leftBoundsNonnegative
        rightBoundsNonnegative (leftNonnegative stage) (ordered stage)
        inductionHypothesis

/-- The backwards-derived range budget contains every forward-propagated
magnitude/error envelope whose initial total fits the input budget. -/
theorem boundsAt_total_le_rangeBudgetAt
    (config : Config depth) (twiddleError : Fin depth → ℝ)
    (initial : Bounds)
    (twiddleErrorNonnegative : ∀ stage, 0 ≤ twiddleError stage)
    (initialFits : initial.total ≤ inputBudget config twiddleError)
    (boundary : Exact.LayerBoundary depth) :
    (boundsAt config twiddleError initial boundary).total ≤
      rangeBudgetAt config twiddleError boundary := by
  induction boundary using Fin.induction with
  | zero =>
      simpa [inputBudget] using initialFits
  | succ stage inductionHypothesis =>
      let previous := boundsAt config twiddleError initial stage.castSucc
      let currentBudget := rangeBudgetAt config twiddleError stage.castSucc
      let followingBudget := rangeBudgetAt config twiddleError stage.succ
      have coefficientPositive : 0 < 2 + twiddleError stage := by
        linarith [twiddleErrorNonnegative stage]
      have localLimit :
          currentBudget ≤
            (followingBudget - arithmeticError (config.butterfly stage)) /
              (2 + twiddleError stage) := by
        dsimp [currentBudget, followingBudget]
        rw [rangeBudgetAt_castSucc]
        exact stageInputBudget_le_nextLimit config twiddleError stage _
      have scaledLocal := (le_div_iff₀ coefficientPositive).mp localLimit
      rw [boundsAt_boundarySucc]
      change (advanceBounds config twiddleError stage previous).total ≤
        followingBudget
      calc
        (advanceBounds config twiddleError stage previous).total =
            (2 + twiddleError stage) * previous.total +
              arithmeticError (config.butterfly stage) := by
          simp [Bounds.total, advanceBounds]
          ring
        _ ≤ (2 + twiddleError stage) * currentBudget +
              arithmeticError (config.butterfly stage) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (by simpa [previous, currentBudget] using inductionHypothesis)
              coefficientPositive.le
          · exact le_rfl
        _ ≤ followingBudget := by nlinarith

/-- The single natural input-budget condition implies every static capacity
condition needed by the no-overflow proof. -/
theorem rangeSafe_of_inputBudget
    (config : Config depth) (twiddleError : Fin depth → ℝ)
    (initial : Bounds)
    (twiddleErrorNonnegative : ∀ stage, 0 ≤ twiddleError stage)
    (initialFits : initial.total ≤ inputBudget config twiddleError)
    (initialPolicy : ∀ stage : Fin depth,
      config.butterfly stage =
        Butterfly.Fixed.Config.initial
          (config.boundaryFormat stage.castSucc).width
          (config.boundaryFormat stage.castSucc).fractionalBits
          (config.twiddleFormat stage).width
          (config.twiddleFormat stage).fractionalBits) :
    RangeSafe config twiddleError initial where
  initialPolicy := initialPolicy
  dataFits stage := by
    let bounds := boundsAt config twiddleError initial stage.castSucc
    let nextBudget := rangeBudgetAt config twiddleError stage.succ
    have envelope : bounds.total ≤
        stageInputBudget config twiddleError stage nextBudget := by
      simpa [bounds, nextBudget] using
        boundsAt_total_le_rangeBudgetAt config twiddleError initial
          twiddleErrorNonnegative initialFits stage.castSucc
    exact envelope.trans
      (stageInputBudget_le_dataCapacity config twiddleError stage nextBudget)
  productFits stage := by
    let bounds := boundsAt config twiddleError initial stage.castSucc
    let nextBudget := rangeBudgetAt config twiddleError stage.succ
    have envelope : bounds.total ≤
        stageInputBudget config twiddleError stage nextBudget := by
      simpa [bounds, nextBudget] using
        boundsAt_total_le_rangeBudgetAt config twiddleError initial
          twiddleErrorNonnegative initialFits stage.castSucc
    have coefficientPositive : 0 < 1 + twiddleError stage := by
      linarith [twiddleErrorNonnegative stage]
    have localLimit := stageInputBudget_le_productLimit config
      twiddleError stage nextBudget
    have scaledLocal := (le_div_iff₀ coefficientPositive).mp localLimit
    dsimp only [Bounds.total] at envelope ⊢
    have scaledEnvelope := mul_le_mul_of_nonneg_right envelope
      coefficientPositive.le
    nlinarith
  outputFits stage := by
    let bounds := boundsAt config twiddleError initial stage.castSucc
    let nextBudget := rangeBudgetAt config twiddleError stage.succ
    have envelope : bounds.total ≤
        stageInputBudget config twiddleError stage nextBudget := by
      simpa [bounds, nextBudget] using
        boundsAt_total_le_rangeBudgetAt config twiddleError initial
          twiddleErrorNonnegative initialFits stage.castSucc
    have coefficientPositive : 0 < 2 + twiddleError stage := by
      linarith [twiddleErrorNonnegative stage]
    have localLimit := stageInputBudget_le_outputLimit config
      twiddleError stage nextBudget
    have scaledLocal := (le_div_iff₀ coefficientPositive).mp localLimit
    dsimp only [Bounds.total] at envelope ⊢
    have scaledEnvelope := mul_le_mul_of_nonneg_right envelope
      coefficientPositive.le
    nlinarith

/-- The usual magnitude/error invariant can be established without an
external no-overflow hypothesis when the formats are statically range-safe. -/
theorem layeredPrefix_bounds_of_rangeSafe
    (config : Config depth) (table : TwiddleTable depth)
    (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (safe : RangeSafe config twiddleError initial)
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
        initial initialNonnegative twiddleAccuracy.error_nonnegative
        stage.castSucc
      have stageNoOverflow := butterflyLayer_noOverflow_of_bounds
        config table twiddleError initial safe stage
        (layeredPrefix config table stage.castSucc fixedInput)
        (Exact.layeredPrefix depth stage.castSucc exactInput)
        inductionHypothesis.1 inductionHypothesis.2 previousNonnegative
        twiddleAccuracy
      rw [boundsAt_boundarySucc, layeredPrefix_boundarySucc,
        Exact.layeredPrefix_boundarySucc]
      constructor
      · exact butterflyLayer_magnitudeBound stage _ inductionHypothesis.1
      · exact butterflyLayer_within config table twiddleError stage _ _ _
          previousNonnegative.1 previousNonnegative.2 twiddleAccuracy
          inductionHypothesis.1 inductionHypothesis.2 stageNoOverflow

/-- Static range safety derives the complete execution-shaped no-overflow
fact used internally by the established numerical correctness theorem. -/
theorem noOverflow_of_rangeSafe
    (config : Config depth) (table : TwiddleTable depth)
    (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (safe : RangeSafe config twiddleError initial) :
    NoOverflow config table fixedInput := by
  intro stage
  have previous := layeredPrefix_bounds_of_rangeSafe config table
    twiddleError fixedInput exactInput initial initialNonnegative
    twiddleAccuracy inputMagnitude inputWithin safe stage.castSucc
  have previousNonnegative := boundsAt_nonnegative config twiddleError
    initial initialNonnegative twiddleAccuracy.error_nonnegative stage.castSucc
  exact butterflyLayer_noOverflow_of_bounds config table twiddleError initial
    safe stage (layeredPrefix config table stage.castSucc fixedInput)
    (Exact.layeredPrefix depth stage.castSucc exactInput)
    previous.1 previous.2 previousNonnegative twiddleAccuracy

/-- End-to-end numerical correctness with no exposed execution-shaped
`NoOverflow` assumption. -/
theorem layeredFFT_within_of_rangeSafe
    (config : Config depth) (table : TwiddleTable depth)
    (twiddleError : Fin depth → ℝ)
    (fixedInput : Vector depth) (exactInput : Exact.Vector depth ℂ)
    (initial : Bounds) (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError)
    (inputMagnitude : MagnitudeBound initial.magnitude exactInput)
    (inputWithin : Within initial.error
      (decodeVector config 0 fixedInput) exactInput)
    (safe : RangeSafe config twiddleError initial) :
    Within
      (boundsAt config twiddleError initial (Fin.last depth)).error
      (decodeVector config (Fin.last depth)
        (layeredFFT config table fixedInput))
      (Exact.layeredFFT depth exactInput) := by
  exact layeredFFT_within config table twiddleError fixedInput exactInput
    initial initialNonnegative twiddleAccuracy inputMagnitude inputWithin
    (noOverflow_of_rangeSafe config table twiddleError fixedInput exactInput
      initial initialNonnegative twiddleAccuracy inputMagnitude inputWithin
      safe)

end HTFFT.Fixed
