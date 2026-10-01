import HTFFT.Fixed.ButterflyRange
import HTFFT.Fixed.Error

namespace HTFFT.Fixed

open HTFFT
open HTFFT.FixedPoint

/-- A uniform symmetric raw-integer component bound for a fixed-point vector.
This is internal proof bookkeeping used to derive hardware representability
from a public decoded-value bound. -/
def VectorBound (bound : Int) (values : Vector depth) : Prop :=
  ∀ index, ComplexBound bound (values index)

theorem vectorBound_of_decodedComponentMagnitude (config : Config depth)
    (boundary : Exact.LayerBoundary depth) (values : Vector depth)
    (bound : Int)
    (decodedBound : ComponentMagnitudeBound
      ((bound : ℝ) / (config.boundaryFormat boundary).scale)
      (decodeVector config boundary values)) :
    VectorBound bound values := by
  intro index
  exact complexBound_of_decode_le _ _ _ (decodedBound index)

theorem vectorBound_of_decodedMagnitude (config : Config depth)
    (boundary : Exact.LayerBoundary depth) (values : Vector depth)
    (bound : Int)
    (decodedBound : MagnitudeBound
      ((bound : ℝ) / (config.boundaryFormat boundary).scale)
      (decodeVector config boundary values)) :
    VectorBound bound values :=
  vectorBound_of_decodedComponentMagnitude config boundary values bound
    decodedBound.component

/-- The conservative raw bound propagated by the initial butterfly policy.
Each layer maps `B` to `3 * B + 1`. -/
def rawBoundAfter (initial : Int) : Nat → Int
  | 0 => initial
  | stage + 1 => 3 * rawBoundAfter initial stage + 1

@[simp]
theorem rawBoundAfter_zero (initial : Int) :
    rawBoundAfter initial 0 = initial :=
  rfl

@[simp]
theorem rawBoundAfter_succ (initial : Int) (stage : Nat) :
    rawBoundAfter initial (stage + 1) =
      3 * rawBoundAfter initial stage + 1 :=
  rfl

theorem VectorBound.bitReverse {bound : Int} {input : Vector depth}
    (bounded : VectorBound bound input) :
    VectorBound bound (Exact.bitReverse input) := by
  intro index
  exact bounded (Exact.bitReverseIndex index)

/-- One layer of an initial-policy fixed-point FFT discharges its own
no-overflow obligations and propagates the uniform raw component bound. -/
theorem butterflyLayer_initial_noOverflow_and_bound
    (depth inputWidth fractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth)
    (dataBound : Int)
    (twiddleFractionalBitsPositive : 0 < twiddleFractionalBits)
    (dataBoundNonnegative : 0 ≤ dataBound)
    (inputBounded : VectorBound dataBound input)
    (twiddleBounded : ∀ offset,
      ComplexBound (2 ^ twiddleFractionalBits : Nat)
        (table.value stage offset))
    (twiddleFits :
      (2 ^ twiddleFractionalBits : Nat) ≤ signedMax twiddleWidth)
    (productFits :
      2 * dataBound + 1 ≤ signedMax (inputWidth + stage.val))
    (outputFits :
      3 * dataBound + 1 ≤ signedMax (inputWidth + stage.val + 1)) :
    let config := Config.initial depth inputWidth fractionalBits twiddleWidth
      twiddleFractionalBits
    LayerNoOverflow config table stage input ∧
      VectorBound (3 * dataBound + 1)
        (butterflyLayer config table stage input) := by
  let config := Config.initial depth inputWidth fractionalBits twiddleWidth
    twiddleFractionalBits
  have butterflyFact
      (group : Fin (2 ^ (depth - stage.val - 1)))
      (offset : Fin (2 ^ stage.val)) :
      Butterfly.Fixed.NoOverflow (config.butterfly stage)
          (input (Exact.layerIndexEquiv depth stage
            { group := group, branch := 0, offset := offset }))
          (input (Exact.layerIndexEquiv depth stage
            { group := group, branch := 1, offset := offset }))
          (table.value stage offset) ∧
        ComplexBound (3 * dataBound + 1)
          (Butterfly.Fixed.butterfly (config.butterfly stage)
            (input (Exact.layerIndexEquiv depth stage
              { group := group, branch := 0, offset := offset }))
            (input (Exact.layerIndexEquiv depth stage
              { group := group, branch := 1, offset := offset }))
            (table.value stage offset)).upper ∧
        ComplexBound (3 * dataBound + 1)
          (Butterfly.Fixed.butterfly (config.butterfly stage)
            (input (Exact.layerIndexEquiv depth stage
              { group := group, branch := 0, offset := offset }))
            (input (Exact.layerIndexEquiv depth stage
              { group := group, branch := 1, offset := offset }))
            (table.value stage offset)).lower := by
    have fact := Butterfly.Fixed.butterfly_initial_noOverflow_and_bound
      (inputWidth + stage.val) fractionalBits twiddleWidth
      twiddleFractionalBits dataBound
      (input (Exact.layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }))
      (input (Exact.layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }))
      (table.value stage offset) twiddleFractionalBitsPositive
      dataBoundNonnegative
      (inputBounded (Exact.layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }))
      (inputBounded (Exact.layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }))
      (twiddleBounded offset) twiddleFits productFits outputFits
    simpa [config, Config.butterfly, Config.initial,
      Butterfly.Fixed.Config.initial, Nat.add_assoc] using fact
  constructor
  · intro group offset
    exact (butterflyFact group offset).1
  · intro outputIndex
    obtain ⟨position, rfl⟩ :=
      (Exact.layerIndexEquiv depth stage).surjective outputIndex
    rcases position with ⟨group, branch, offset⟩
    by_cases branchZero : branch = 0
    · subst branch
      rw [butterflyLayer_first]
      exact (butterflyFact group offset).2.1
    · have branchOne : branch = 1 := by
        apply Fin.ext
        omega
      subst branch
      rw [butterflyLayer_second]
      exact (butterflyFact group offset).2.2

/-- Capacity assumptions sufficient to run every layer of an initial-policy
network from a selected raw input bound. -/
def InitialRangeSafe (depth inputWidth twiddleWidth twiddleFractionalBits : Nat)
    (initialBound : Int) : Prop :=
  0 < twiddleFractionalBits ∧
    0 ≤ initialBound ∧
    (2 ^ twiddleFractionalBits : Nat) ≤ signedMax twiddleWidth ∧
    ∀ stage : Fin depth,
      2 * rawBoundAfter initialBound stage.val + 1 ≤
          signedMax (inputWidth + stage.val) ∧
        3 * rawBoundAfter initialBound stage.val + 1 ≤
          signedMax (inputWidth + stage.val + 1)

theorem rawBoundAfter_nonnegative {initial : Int}
    (initialNonnegative : 0 ≤ initial) (stage : Nat) :
    0 ≤ rawBoundAfter initial stage := by
  induction stage with
  | zero => exact initialNonnegative
  | succ stage inductionHypothesis =>
      rw [rawBoundAfter_succ]
      omega

/-- Every prefix of a safe initial-policy network satisfies its recursively
propagated raw component bound. -/
theorem layeredPrefix_initial_bound
    (depth inputWidth fractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (table : TwiddleTable depth) (input : Vector depth) (initialBound : Int)
    (inputBounded : VectorBound initialBound input)
    (twiddleBounded : ∀ stage offset,
      ComplexBound (2 ^ twiddleFractionalBits : Nat)
        (table.value stage offset))
    (safe : InitialRangeSafe depth inputWidth twiddleWidth
      twiddleFractionalBits initialBound)
    (boundary : Exact.LayerBoundary depth) :
    VectorBound (rawBoundAfter initialBound boundary.val)
      (layeredPrefix
        (Config.initial depth inputWidth fractionalBits twiddleWidth
          twiddleFractionalBits)
        table boundary input) := by
  let config := Config.initial depth inputWidth fractionalBits twiddleWidth
    twiddleFractionalBits
  induction boundary using Fin.induction with
  | zero =>
      simpa [config] using inputBounded.bitReverse
  | succ stage inductionHypothesis =>
      rw [layeredPrefix_boundarySucc]
      change VectorBound
        (rawBoundAfter initialBound (stage.val + 1))
        (butterflyLayer config table stage
          (layeredPrefix config table stage.castSucc input))
      rw [rawBoundAfter_succ]
      exact (butterflyLayer_initial_noOverflow_and_bound depth inputWidth
        fractionalBits twiddleWidth twiddleFractionalBits table stage
        (layeredPrefix config table stage.castSucc input)
        (rawBoundAfter initialBound stage.val) safe.1
        (rawBoundAfter_nonnegative safe.2.1 stage.val) inductionHypothesis
        (twiddleBounded stage) safe.2.2.1 (safe.2.2.2 stage).1
        (safe.2.2.2 stage).2).2

/-- A natural input raw bound plus static format-capacity checks imply the
complete trace-shaped no-overflow predicate required by numerical correctness. -/
theorem noOverflow_initial_of_bound
    (depth inputWidth fractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (table : TwiddleTable depth) (input : Vector depth) (initialBound : Int)
    (inputBounded : VectorBound initialBound input)
    (twiddleBounded : ∀ stage offset,
      ComplexBound (2 ^ twiddleFractionalBits : Nat)
        (table.value stage offset))
    (safe : InitialRangeSafe depth inputWidth twiddleWidth
      twiddleFractionalBits initialBound) :
    NoOverflow
      (Config.initial depth inputWidth fractionalBits twiddleWidth
        twiddleFractionalBits)
      table input := by
  intro stage
  exact (butterflyLayer_initial_noOverflow_and_bound depth inputWidth
    fractionalBits twiddleWidth twiddleFractionalBits table stage
    (layeredPrefix
      (Config.initial depth inputWidth fractionalBits twiddleWidth
        twiddleFractionalBits)
      table stage.castSucc input)
    (rawBoundAfter initialBound stage.val) safe.1
    (rawBoundAfter_nonnegative safe.2.1 stage.val)
    (layeredPrefix_initial_bound depth inputWidth fractionalBits twiddleWidth
      twiddleFractionalBits table input initialBound inputBounded twiddleBounded
      safe stage.castSucc)
    (twiddleBounded stage) safe.2.2.1 (safe.2.2.2 stage).1
    (safe.2.2.2 stage).2).1

/-! ## Numerical range safety

The raw recurrence above remains useful for small concrete arithmetic tests.
The public FFT proof uses the following tighter criterion instead.  It shares
the same `Bounds` recurrence as the accuracy proof, so range grows with the
actual radix-two magnitude/error analysis rather than an unrelated `3^s`
estimate. -/

/-- Static capacity conditions sufficient for the approved FFT arithmetic
policy.  At stage `s`, `magnitude + error` bounds the decoded hardware data,
and `1 + twiddleError s` bounds the decoded stored twiddle. -/
structure RangeSafe (config : Config depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds) : Prop where
  initialPolicy : ∀ stage : Fin depth,
    config.butterfly stage =
      Butterfly.Fixed.Config.initial
        (config.boundaryFormat stage.castSucc).width
        (config.boundaryFormat stage.castSucc).fractionalBits
        (config.twiddleFormat stage).width
        (config.twiddleFormat stage).fractionalBits
  dataFits : ∀ stage : Fin depth,
    let bounds := boundsAt config twiddleError initial stage.castSucc
    bounds.magnitude + bounds.error ≤
      decodedCapacity (config.boundaryFormat stage.castSucc)
  productFits : ∀ stage : Fin depth,
    let bounds := boundsAt config twiddleError initial stage.castSucc
    let dataMagnitude := bounds.magnitude + bounds.error
    dataMagnitude * (1 + twiddleError stage) +
        quantum (config.boundaryFormat stage.castSucc) ≤
      decodedCapacity (config.boundaryFormat stage.castSucc)
  outputFits : ∀ stage : Fin depth,
    let bounds := boundsAt config twiddleError initial stage.castSucc
    let dataMagnitude := bounds.magnitude + bounds.error
    dataMagnitude +
          (dataMagnitude * (1 + twiddleError stage) +
            quantum (config.boundaryFormat stage.castSucc)) ≤
      decodedCapacity (config.boundaryFormat stage.succ)

/-- Largest incoming decoded envelope admitted by one stage, given an
admissible envelope at the following boundary.  The four terms respectively
reserve room for the stage input, rounded product, butterfly output, and the
complete propagated accuracy envelope. -/
noncomputable def stageInputBudget (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth)
    (nextBudget : ℝ) : ℝ :=
  let dataCapacity := decodedCapacity
    (config.boundaryFormat stage.castSucc)
  let outputCapacity := decodedCapacity
    (config.boundaryFormat stage.succ)
  let productQuantum := quantum
    (config.boundaryFormat stage.castSucc)
  let coefficient := 1 + twiddleError stage
  let outputCoefficient := 2 + twiddleError stage
  min dataCapacity
    (min ((dataCapacity - productQuantum) / coefficient)
      (min ((outputCapacity - productQuantum) / outputCoefficient)
        ((nextBudget - arithmeticError (config.butterfly stage)) /
          outputCoefficient)))

/-- Safe decoded envelope at a layer boundary, computed backwards from the
final output format. -/
noncomputable def rangeBudgetAt (config : Config depth)
    (twiddleError : Fin depth → ℝ)
    (boundary : Exact.LayerBoundary depth) : ℝ :=
  (Exact.butterflyStageSuffix depth boundary).foldr
    (fun stage next => stageInputBudget config twiddleError stage next)
    (decodedCapacity (config.boundaryFormat (Fin.last depth)))

/-- The natural input envelope admitted by all derived intermediate formats. -/
noncomputable def inputBudget (config : Config depth)
    (twiddleError : Fin depth → ℝ) : ℝ :=
  rangeBudgetAt config twiddleError 0

@[simp] theorem rangeBudgetAt_castSucc (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) :
    rangeBudgetAt config twiddleError stage.castSucc =
      stageInputBudget config twiddleError stage
        (rangeBudgetAt config twiddleError stage.succ) := by
  simp [rangeBudgetAt, Exact.butterflyStageSuffix_castSucc]

theorem stageInputBudget_le_dataCapacity (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) (nextBudget : ℝ) :
    stageInputBudget config twiddleError stage nextBudget ≤
      decodedCapacity (config.boundaryFormat stage.castSucc) := by
  exact min_le_left _ _

theorem stageInputBudget_le_productLimit (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) (nextBudget : ℝ) :
    stageInputBudget config twiddleError stage nextBudget ≤
      (decodedCapacity (config.boundaryFormat stage.castSucc) -
          quantum (config.boundaryFormat stage.castSucc)) /
        (1 + twiddleError stage) := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem stageInputBudget_le_outputLimit (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) (nextBudget : ℝ) :
    stageInputBudget config twiddleError stage nextBudget ≤
      (decodedCapacity (config.boundaryFormat stage.succ) -
          quantum (config.boundaryFormat stage.castSucc)) /
        (2 + twiddleError stage) := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem stageInputBudget_le_nextLimit (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth) (nextBudget : ℝ) :
    stageInputBudget config twiddleError stage nextBudget ≤
      (nextBudget - arithmeticError (config.butterfly stage)) /
        (2 + twiddleError stage) := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))

/-- A decoded value close to an exact value of bounded magnitude has magnitude
at most the sum of those two bounds. -/
theorem norm_decode_le_magnitude_add_error
    {format : Format} {fixed : HTFFT.Complex Int} {exact : ℂ}
    {magnitude error : ℝ}
    (exactMagnitude : ‖exact‖ ≤ magnitude)
    (close : ‖decodeComplex format fixed - exact‖ ≤ error) :
    ‖decodeComplex format fixed‖ ≤ magnitude + error := by
  calc
    ‖decodeComplex format fixed‖ =
        ‖(decodeComplex format fixed - exact) + exact‖ := by
      congr 1
      ring
    _ ≤ ‖decodeComplex format fixed - exact‖ + ‖exact‖ :=
      norm_add_le _ _
    _ ≤ error + magnitude := add_le_add close exactMagnitude
    _ = magnitude + error := by ring

/-- One stage's natural exact-magnitude/error invariant and its static
capacity certificate derive the concrete local no-overflow predicate. -/
theorem butterflyLayer_noOverflow_of_bounds
    (config : Config depth) (table : TwiddleTable depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds)
    (safe : RangeSafe config twiddleError initial)
    (stage : Fin depth) (fixedInput : Vector depth)
    (exactInput : Exact.Vector depth ℂ)
    (inputMagnitude : MagnitudeBound
      (boundsAt config twiddleError initial stage.castSucc).magnitude
      exactInput)
    (inputWithin : Within
      (boundsAt config twiddleError initial stage.castSucc).error
      (decodeVector config stage.castSucc fixedInput) exactInput)
    (boundsNonnegative :
      (boundsAt config twiddleError initial stage.castSucc).Nonnegative)
    (twiddleAccuracy : TwiddleAccuracy config table twiddleError) :
    LayerNoOverflow config table stage fixedInput := by
  intro group offset
  let firstIndex := Exact.layerIndexEquiv depth stage
    { group := group, branch := 0, offset := offset }
  let secondIndex := Exact.layerIndexEquiv depth stage
    { group := group, branch := 1, offset := offset }
  let bounds := boundsAt config twiddleError initial stage.castSucc
  let dataMagnitude := bounds.magnitude + bounds.error
  let twiddleMagnitude := 1 + twiddleError stage
  have dataMagnitudeNonnegative : 0 ≤ dataMagnitude := by
    dsimp [dataMagnitude, bounds]
    exact add_nonneg boundsNonnegative.1 boundsNonnegative.2
  have firstBounded :
      ‖decodeComplex (config.boundaryFormat stage.castSucc)
          (fixedInput firstIndex)‖ ≤ dataMagnitude := by
    exact norm_decode_le_magnitude_add_error
      (inputMagnitude firstIndex)
      (by simpa [decodeVector] using inputWithin firstIndex)
  have secondBounded :
      ‖decodeComplex (config.boundaryFormat stage.castSucc)
          (fixedInput secondIndex)‖ ≤ dataMagnitude := by
    exact norm_decode_le_magnitude_add_error
      (inputMagnitude secondIndex)
      (by simpa [decodeVector] using inputWithin secondIndex)
  have twiddleBounded :
      ‖decodeComplex (config.twiddleFormat stage)
          (table.value stage offset)‖ ≤ twiddleMagnitude := by
    calc
      ‖decodeComplex (config.twiddleFormat stage)
          (table.value stage offset)‖ =
          ‖(decodeComplex (config.twiddleFormat stage)
              (table.value stage offset) - exactTwiddle stage offset) +
            exactTwiddle stage offset‖ := by
        congr 1
        ring
      _ ≤ ‖decodeComplex (config.twiddleFormat stage)
              (table.value stage offset) - exactTwiddle stage offset‖ +
            ‖exactTwiddle stage offset‖ := norm_add_le _ _
      _ ≤ twiddleError stage + 1 := by
        exact add_le_add (twiddleAccuracy.accurate stage offset)
          (le_of_eq (norm_exactTwiddle stage offset))
      _ = twiddleMagnitude := by simp [twiddleMagnitude, add_comm]
  have outputFormatEq :
      config.boundaryFormat stage.succ =
        ⟨(config.boundaryFormat stage.castSucc).width + 1,
          (config.boundaryFormat stage.castSucc).fractionalBits⟩ := by
    have equality := congrArg Butterfly.Fixed.Config.outputFormat
      (safe.initialPolicy stage)
    simpa [Config.butterfly, Butterfly.Fixed.Config.initial] using equality
  have outputCapacity := safe.outputFits stage
  rw [outputFormatEq] at outputCapacity
  rw [safe.initialPolicy stage]
  exact Butterfly.Fixed.noOverflow_initial_of_magnitudes
    (config.boundaryFormat stage.castSucc).width
    (config.boundaryFormat stage.castSucc).fractionalBits
    (config.twiddleFormat stage).width
    (config.twiddleFormat stage).fractionalBits
    (fixedInput firstIndex) (fixedInput secondIndex)
    (table.value stage offset) dataMagnitude twiddleMagnitude
    dataMagnitudeNonnegative firstBounded secondBounded twiddleBounded
    (twiddleAccuracy.fits stage offset)
    (by simpa [dataMagnitude, bounds] using safe.dataFits stage)
    (by simpa [dataMagnitude, twiddleMagnitude, bounds] using
      safe.productFits stage)
    (by simpa [dataMagnitude, twiddleMagnitude, bounds] using
      outputCapacity)

end HTFFT.Fixed
