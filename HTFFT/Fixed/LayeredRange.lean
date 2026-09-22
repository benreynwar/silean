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

/-- Convert a natural decoded componentwise magnitude bound back into the
corresponding raw-integer bound. -/
theorem complexBound_of_decode_le (format : Format)
    (value : HTFFT.Complex Int) (bound : Int)
    (decodedBound :
      componentNorm (decodeComplex format value) ≤
        (bound : ℝ) / format.scale) :
    ComplexBound bound value := by
  have scalePositive : (0 : ℝ) < format.scale := by
    simp [Format.scale]
  have realPart :
      (decodeComplex format value).re =
        (value.real : ℝ) / format.scale := by
    simp only [decodeComplex, FixedPoint.decodeComplex, HTFFT.Complex.map,
      FixedPoint.decode,
      rationalComplexToComplex_re]
    rw [Rat.cast_divInt]
    norm_cast
  have imagPart :
      (decodeComplex format value).im =
        (value.imag : ℝ) / format.scale := by
    simp only [decodeComplex, FixedPoint.decodeComplex, HTFFT.Complex.map,
      FixedPoint.decode,
      rationalComplexToComplex_im]
    rw [Rat.cast_divInt]
    norm_cast
  have realDecoded :=
    (abs_re_le_componentNorm (decodeComplex format value)).trans decodedBound
  have imagDecoded :=
    (abs_im_le_componentNorm (decodeComplex format value)).trans decodedBound
  rw [realPart, abs_div, abs_of_pos scalePositive] at realDecoded
  rw [imagPart, abs_div, abs_of_pos scalePositive] at imagDecoded
  have realRaw : |(value.real : ℝ)| ≤ bound := by
    apply (div_le_div_iff_of_pos_right scalePositive).mp
    simpa using realDecoded
  have imagRaw : |(value.imag : ℝ)| ≤ bound := by
    apply (div_le_div_iff_of_pos_right scalePositive).mp
    simpa using imagDecoded
  constructor
  · exact_mod_cast realRaw
  · exact_mod_cast imagRaw

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

end HTFFT.Fixed
