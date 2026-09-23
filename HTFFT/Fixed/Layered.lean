import HTFFT.Butterfly
import HTFFT.Exact.Layered
import Mathlib.Analysis.Complex.Basic

namespace HTFFT.Fixed

open HTFFT
open HTFFT.FixedPoint

/-- Raw fixed-point samples at one boundary of a depth-`depth` FFT.  The
format is carried by `Config.boundaryFormat`, rather than repeated in every
sample. -/
abbrev Vector (depth : Nat) := Fin (2 ^ depth) → HTFFT.Complex Int

/-- Formats and rounding choices for a pure fixed-point layered FFT.

There is one data format at each layer boundary, including the input and final
output boundaries.  Consequently stage `s` consumes `boundaryFormat s` and
produces `boundaryFormat (s + 1)` by construction. -/
structure Config (depth : Nat) where
  boundaryFormat : Exact.LayerBoundary depth → Format
  twiddleFormat : Fin depth → Format
  productFormat : Fin depth → Format
  rounding : Fin depth → RoundingMode

/-- The existing fixed-point butterfly configuration induced at one stage. -/
def Config.butterfly (config : Config depth) (stage : Fin depth) :
    Butterfly.Fixed.Config :=
  { dataFormat := config.boundaryFormat stage.castSucc
    twiddleFormat := config.twiddleFormat stage
    productFormat := config.productFormat stage
    outputFormat := config.boundaryFormat stage.succ
    rounding := config.rounding stage }

/-- Initial format policy: retain the input binary point and add one signed
component bit at every butterfly layer.  Products retain the data format at
the input of their stage. -/
def Config.initial (depth inputWidth fractionalBits twiddleWidth
    twiddleFractionalBits : Nat) : Config depth where
  boundaryFormat boundary := ⟨inputWidth + boundary.val, fractionalBits⟩
  twiddleFormat _ := ⟨twiddleWidth, twiddleFractionalBits⟩
  productFormat stage := ⟨inputWidth + stage.val, fractionalBits⟩
  rounding _ := .nearestTiesToEven

/-- Stored twiddles used by each layer.  Stage `s` has `2^s` distinct
twiddles, shared by every group in that layer. -/
structure TwiddleTable (depth : Nat) where
  value : (stage : Fin depth) →
    Fin (2 ^ stage.val) → HTFFT.Complex Int

/-- The exact twiddle corresponding to a stored stage-table entry. -/
noncomputable def exactTwiddle (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) : ℂ :=
  Exact.twiddle (stage.val + 1)
    (Exact.halfIndexEquiv stage.val (Sum.inl offset))

/-- Embed the project's rational complex values into Mathlib's complex
numbers.  This is the sole numerical boundary used to compare fixed-point
values with the exact FFT. -/
noncomputable def rationalComplexToComplex (value : HTFFT.Complex Rat) : ℂ :=
  (value.real : ℂ) + (value.imag : ℂ) * Complex.I

/-- Decode a raw fixed-point complex value directly into Mathlib's `ℂ`. -/
noncomputable def decodeComplex (format : Format)
    (value : HTFFT.Complex Int) : ℂ :=
  rationalComplexToComplex (FixedPoint.decodeComplex format value)

/-- The maximum absolute component of a complex value.  This deliberately
uses a conservative componentwise norm: it matches signed component formats
and keeps representability and rounding bounds explicit. -/
noncomputable def componentNorm (value : ℂ) : ℝ :=
  max |value.re| |value.im|

/-- A pointwise Euclidean complex-magnitude bound for a vector. -/
def MagnitudeBound (bound : ℝ) (values : Fin count → ℂ) : Prop :=
  ∀ index, ‖values index‖ ≤ bound

/-- A componentwise magnitude bound retained for fixed-width range reasoning.
Numerical error propagation uses `MagnitudeBound` instead. -/
def ComponentMagnitudeBound (bound : ℝ) (values : Fin count → ℂ) : Prop :=
  ∀ index, componentNorm (values index) ≤ bound

/-- A pointwise Euclidean complex error bound between two vectors. -/
def Within (bound : ℝ) (actual expected : Fin count → ℂ) : Prop :=
  ∀ index, ‖actual index - expected index‖ ≤ bound

/-- Decode all samples at a selected network boundary. -/
noncomputable def decodeVector (config : Config depth)
    (boundary : Exact.LayerBoundary depth) (values : Vector depth) :
    Fin (2 ^ depth) → ℂ :=
  fun index => decodeComplex (config.boundaryFormat boundary) (values index)

/-- Every raw component in a vector is representable in the format assigned to
the selected layer boundary. -/
def VectorFits (config : Config depth)
    (boundary : Exact.LayerBoundary depth) (values : Vector depth) : Prop :=
  ∀ index, ComplexFits (config.boundaryFormat boundary) (values index)

/-- Quantize a rational-complex input vector into the configured input
format. Overflow remains explicit and is not applied here. -/
def encodeInput (config : Config depth) (rounding : RoundingMode)
    (values : Fin (2 ^ depth) → HTFFT.Complex Rat) : Vector depth :=
  fun index => FixedPoint.encodeComplex rounding (config.boundaryFormat 0)
    (values index)

/-- Embed a rational-complex input vector into the exact complex domain. -/
noncomputable def rationalInputToComplex
    (values : Fin (2 ^ depth) → HTFFT.Complex Rat) : Exact.Vector depth ℂ :=
  fun index => rationalComplexToComplex (values index)

/-- Decode a stored twiddle using the format selected for its layer. -/
noncomputable def decodeTwiddle (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) : ℂ :=
  decodeComplex (config.twiddleFormat stage) (table.value stage offset)

/-- A certificate is separate from the stored table itself. It records both
that each table entry is representable and a uniform Euclidean complex error
for each stage. -/
structure TwiddleAccuracy (config : Config depth)
    (table : TwiddleTable depth) (error : Fin depth → ℝ) : Prop where
  error_nonnegative : ∀ stage, 0 ≤ error stage
  fits : ∀ stage offset,
    ComplexFits (config.twiddleFormat stage) (table.value stage offset)
  accurate : ∀ stage offset,
    ‖decodeTwiddle config table stage offset - exactTwiddle stage offset‖ ≤
      error stage

/-- One fixed-point layer, using exactly the same group/branch/offset indexing
as the certified exact network. -/
def butterflyLayer (config : Config depth) (table : TwiddleTable depth)
    (stage : Fin depth) (input : Vector depth) : Vector depth :=
  fun outputIndex =>
    let position := (Exact.layerIndexEquiv depth stage).symm outputIndex
    let firstIndex := Exact.layerIndexEquiv depth stage
      { position with branch := 0 }
    let secondIndex := Exact.layerIndexEquiv depth stage
      { position with branch := 1 }
    let result := Butterfly.Fixed.butterfly (config.butterfly stage)
      (input firstIndex) (input secondIndex) (table.value stage position.offset)
    if position.branch = 0 then result.upper else result.lower

@[simp]
theorem butterflyLayer_first (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth)
    (group : Fin (2 ^ (depth - stage.val - 1)))
    (offset : Fin (2 ^ stage.val)) :
    butterflyLayer config table stage input
        (Exact.layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }) =
      (Butterfly.Fixed.butterfly (config.butterfly stage)
        (input (Exact.layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }))
        (input (Exact.layerIndexEquiv depth stage
          { group := group, branch := 1, offset := offset }))
        (table.value stage offset)).upper := by
  simp [butterflyLayer]

@[simp]
theorem butterflyLayer_second (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth)
    (group : Fin (2 ^ (depth - stage.val - 1)))
    (offset : Fin (2 ^ stage.val)) :
    butterflyLayer config table stage input
        (Exact.layerIndexEquiv depth stage
          { group := group, branch := 1, offset := offset }) =
      (Butterfly.Fixed.butterfly (config.butterfly stage)
        (input (Exact.layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }))
        (input (Exact.layerIndexEquiv depth stage
          { group := group, branch := 1, offset := offset }))
        (table.value stage offset)).lower := by
  simp [butterflyLayer]

/-- A fixed-point butterfly layer already stores every output in the
canonical signed representative of its output format. -/
theorem wrapComplex_butterflyLayer (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth) :
    (fun index => Butterfly.Fixed.wrapComplex
      (config.boundaryFormat stage.succ)
      (butterflyLayer config table stage input index)) =
      butterflyLayer config table stage input := by
  funext outputIndex
  let position := (Exact.layerIndexEquiv depth stage).symm outputIndex
  by_cases upper : position.branch = 0
  · simp [butterflyLayer, position, upper, Butterfly.Fixed.butterfly,
      Config.butterfly]
  · simp [butterflyLayer, position, upper, Butterfly.Fixed.butterfly,
      Config.butterfly]

/-- Apply an explicitly selected sequence of fixed-point layers. -/
def applyButterflyLayers (config : Config depth) (table : TwiddleTable depth)
    (stages : List (Fin depth)) (input : Vector depth) : Vector depth :=
  stages.foldl (fun current stage =>
    butterflyLayer config table stage current) input

@[simp]
theorem applyButterflyLayers_nil (config : Config depth)
    (table : TwiddleTable depth) (input : Vector depth) :
    applyButterflyLayers config table [] input = input :=
  rfl

theorem applyButterflyLayers_append (config : Config depth)
    (table : TwiddleTable depth) (first second : List (Fin depth))
    (input : Vector depth) :
    applyButterflyLayers config table (first ++ second) input =
      applyButterflyLayers config table second
        (applyButterflyLayers config table first input) := by
  simp [applyButterflyLayers, List.foldl_append]

/-- The pure fixed-point FFT: bit-reverse the raw input and apply the same
ascending layer sequence as the exact network. -/
def layeredFFT (config : Config depth) (table : TwiddleTable depth)
    (input : Vector depth) : Vector depth :=
  applyButterflyLayers config table (Exact.butterflyStages depth)
    (Exact.bitReverse input)

/-- The fixed-point state after `boundary` completed layers. -/
def layeredPrefix (config : Config depth) (table : TwiddleTable depth)
    (boundary : Exact.LayerBoundary depth) (input : Vector depth) :
    Vector depth :=
  applyButterflyLayers config table
    (Exact.butterflyStagePrefix depth boundary) (Exact.bitReverse input)

/-- Apply the layers after `boundary` to an intermediate fixed-point state. -/
def layeredSuffix (config : Config depth) (table : TwiddleTable depth)
    (boundary : Exact.LayerBoundary depth) (input : Vector depth) :
    Vector depth :=
  applyButterflyLayers config table
    (Exact.butterflyStageSuffix depth boundary) input

@[simp]
theorem layeredPrefix_zero (config : Config depth)
    (table : TwiddleTable depth) (input : Vector depth) :
    layeredPrefix config table 0 input = Exact.bitReverse input :=
  rfl

@[simp]
theorem layeredPrefix_final (config : Config depth)
    (table : TwiddleTable depth) (input : Vector depth) :
    layeredPrefix config table (Fin.last depth) input =
      layeredFFT config table input := by
  unfold layeredPrefix Exact.butterflyStagePrefix layeredFFT
    Exact.butterflyStages
  have stages : List.take (Fin.last depth).val (List.finRange depth) =
      List.finRange depth := by
    change List.take depth (List.finRange depth) = List.finRange depth
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange depth))
  rw [stages]

/-- Advancing a fixed prefix boundary applies exactly one additional layer. -/
theorem layeredPrefix_boundarySucc (config : Config depth)
    (table : TwiddleTable depth) (stage : Fin depth) (input : Vector depth) :
    layeredPrefix config table stage.succ input =
      butterflyLayer config table stage
        (layeredPrefix config table stage.castSucc input) := by
  rw [layeredPrefix, Exact.butterflyStagePrefix_boundarySucc,
    applyButterflyLayers_append]
  rfl

/-- Canonical signed representatives remain canonical while an ascending
prefix of butterfly stages is applied to an already reordered vector. -/
theorem wrapComplex_applyButterflyStagePrefix_of_canonical
    (config : Config depth) (table : TwiddleTable depth)
    (input : Vector depth)
    (inputCanonical :
      (fun index => Butterfly.Fixed.wrapComplex (config.boundaryFormat 0)
        (input index)) = input)
    (boundary : Exact.LayerBoundary depth) :
    (fun index => Butterfly.Fixed.wrapComplex
      (config.boundaryFormat boundary)
      (applyButterflyLayers config table
        (Exact.butterflyStagePrefix depth boundary) input index)) =
      applyButterflyLayers config table
        (Exact.butterflyStagePrefix depth boundary) input := by
  induction boundary using Fin.induction with
  | zero =>
      simpa [Exact.butterflyStagePrefix, Exact.butterflyStages] using
        inputCanonical
  | succ stage _ =>
      rw [Exact.butterflyStagePrefix_boundarySucc,
        applyButterflyLayers_append]
      exact wrapComplex_butterflyLayer config table stage _

/-- Canonical signed representatives remain canonical through every prefix of
the fixed-point network.  The only assumption is that the supplied input is
already canonical at boundary zero. -/
theorem wrapComplex_layeredPrefix_of_canonical
    (config : Config depth) (table : TwiddleTable depth)
    (input : Vector depth)
    (inputCanonical :
      (fun index => Butterfly.Fixed.wrapComplex (config.boundaryFormat 0)
        (input index)) = input)
    (boundary : Exact.LayerBoundary depth) :
    (fun index => Butterfly.Fixed.wrapComplex
      (config.boundaryFormat boundary)
      (layeredPrefix config table boundary input index)) =
      layeredPrefix config table boundary input := by
  have reversedCanonical :
      (fun index => Butterfly.Fixed.wrapComplex (config.boundaryFormat 0)
        (Exact.bitReverse input index)) = Exact.bitReverse input := by
    funext index
    exact congrFun inputCanonical (Exact.bitReverseIndex index)
  exact wrapComplex_applyButterflyStagePrefix_of_canonical config table
    (Exact.bitReverse input) reversedCanonical boundary

/-- The complete fixed-point FFT is canonical whenever its input words are
canonical. -/
theorem wrapComplex_layeredFFT_of_canonical
    (config : Config depth) (table : TwiddleTable depth)
    (input : Vector depth)
    (inputCanonical :
      (fun index => Butterfly.Fixed.wrapComplex (config.boundaryFormat 0)
        (input index)) = input) :
    (fun index => Butterfly.Fixed.wrapComplex
      (config.boundaryFormat (Fin.last depth))
      (layeredFFT config table input index)) =
      layeredFFT config table input := by
  simpa only [layeredPrefix_final] using
    wrapComplex_layeredPrefix_of_canonical config table input
      inputCanonical (Fin.last depth)

/-- Splitting the pure fixed-point layer sequence does not change its result. -/
theorem layeredFFT_split (config : Config depth) (table : TwiddleTable depth)
    (boundary : Exact.LayerBoundary depth) (input : Vector depth) :
    layeredFFT config table input =
      layeredSuffix config table boundary
        (layeredPrefix config table boundary input) := by
  rw [layeredFFT,
    ← List.take_append_drop boundary.val (Exact.butterflyStages depth),
    applyButterflyLayers_append, layeredSuffix]
  rfl

/-- No fixed-width boundary in a selected layer changes its mathematical
integer input. -/
def LayerNoOverflow (config : Config depth) (table : TwiddleTable depth)
    (stage : Fin depth) (input : Vector depth) : Prop :=
  ∀ group offset,
    Butterfly.Fixed.NoOverflow (config.butterfly stage)
      (input (Exact.layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }))
      (input (Exact.layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }))
      (table.value stage offset)

/-- Every layer of a complete execution is free of fixed-width overflow. -/
def NoOverflow (config : Config depth) (table : TwiddleTable depth)
    (input : Vector depth) : Prop :=
  ∀ stage,
    LayerNoOverflow config table stage
      (layeredPrefix config table stage.castSucc input)

/-- Conservative scalar bounds carried from one layer boundary to the next. -/
structure Bounds where
  magnitude : ℝ
  error : ℝ

def Bounds.Nonnegative (bounds : Bounds) : Prop :=
  0 ≤ bounds.magnitude ∧ 0 ≤ bounds.error

/-- The value of one least-significant bit after decoding a format. -/
noncomputable def quantum (format : Format) : ℝ :=
  1 / (2 : ℝ) ^ format.fractionalBits

/-- A conservative per-component allowance for the three rounding sites on
each butterfly output: input alignment, fused complex multiplication, and
output conversion. -/
noncomputable def componentArithmeticError
    (config : Butterfly.Fixed.Config) : ℝ :=
  2 * quantum config.productFormat + quantum config.outputFormat

/-- Convert the per-component arithmetic allowance to Euclidean complex
magnitude. -/
noncomputable def arithmeticError (config : Butterfly.Fixed.Config) : ℝ :=
  Real.sqrt 2 * componentArithmeticError config

/-- Advance the uniform exact-magnitude and fixed-point error bounds through
one layer. Exact roots of unity have norm one, so exact magnitudes grow by at
most two. Existing data error is multiplied by at most `2 + delta`; twiddle
error and local arithmetic rounding contribute separately. -/
noncomputable def advanceBounds (config : Config depth)
    (twiddleError : Fin depth → ℝ) (stage : Fin depth)
    (bounds : Bounds) : Bounds :=
  { magnitude := 2 * bounds.magnitude
    error := (2 + twiddleError stage) * bounds.error +
      bounds.magnitude * twiddleError stage +
      arithmeticError (config.butterfly stage) }

/-- Bounds after the selected number of layers.  This is the public `M_s` and
`E_s` recurrence; stage-dependent formats and twiddle errors are folded in
execution order. -/
noncomputable def boundsAt (config : Config depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds)
    (boundary : Exact.LayerBoundary depth) : Bounds :=
  (Exact.butterflyStagePrefix depth boundary).foldl
    (fun bounds stage => advanceBounds config twiddleError stage bounds) initial

/-- Advancing a boundary advances the scalar bounds through that stage. -/
theorem boundsAt_boundarySucc (config : Config depth)
    (twiddleError : Fin depth → ℝ) (initial : Bounds) (stage : Fin depth) :
    boundsAt config twiddleError initial stage.succ =
      advanceBounds config twiddleError stage
        (boundsAt config twiddleError initial stage.castSucc) := by
  rw [boundsAt, Exact.butterflyStagePrefix_boundarySucc, List.foldl_append]
  rfl

end HTFFT.Fixed
