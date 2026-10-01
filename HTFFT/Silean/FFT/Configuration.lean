import HTFFT.Silean.FFTStage.FFTStage
import HTFFT.Silean.UnrolledFFT.Configuration
import HTFFT.Fixed.TwiddleGeneratorCorrectness
import HTFFT.Fixed.LayeredRangeCorrectness
import Silean.Modules.BarrelShifter.BarrelShifter

/-! # Complete streamed FFT configuration

The complete FFT has `2 ^ depth` samples and carries `2 ^ laneDepth` samples
per cycle. Numeric formats are shared by the unrolled prefix and rolled
suffix. Pipeline placements and frame-storage latencies are explicit static
choices; the rolled-chain latency is derived from its concrete stages.
-/

namespace HTFFT.Silean.FFT

/-- User-authored choices for the complete mixed unrolled/streamed FFT.
Proposition-valued fields certify that those choices describe the supported
geometry; arithmetic formats, twiddle data, latency, range, and error bounds
are all derived below. -/
structure Configuration (depth : Nat) where
  inputFormat : FixedPoint.Format
  /-- Fractional precision of each generated signed-Q2 twiddle table. -/
  twiddleFractionalBits : Fin depth → Nat
  twiddleFractionalBits_min : ∀ stage, 2 ≤ twiddleFractionalBits stage
  laneDepth : Nat
  laneDepth_pos : 0 < laneDepth
  laneDepth_le_depth : laneDepth ≤ depth
  initialReorderGeometry : 2 * laneDepth ≤ depth
  initialBarrelPipeline :
    _root_.Silean.Modules.BarrelShifter.Pipeline laneDepth
  unrolledButterflyPipeline : Fin laneDepth →
    PipelinedFixedButterfly.Pipeline
  unrolledBoundaryLatency : HTFFT.Exact.LayerBoundary laneDepth → Nat
  rolledButterflyPipeline : Fin (depth - laneDepth) →
    PipelinedFixedButterfly.Pipeline
  rolledTwiddleDefinitionName : Fin (depth - laneDepth) → String

/-- Arithmetic formats are derived from the supported FFT policy: data gains
one high bit per layer and twiddles use signed Q2 storage. -/
def Configuration.arithmetic (configuration : Configuration depth) :
    FFTConfiguration depth where
  inputFormat := configuration.inputFormat
  twiddleFormat stage :=
    HTFFT.Fixed.TwiddleGenerator.q2Format
      (configuration.twiddleFractionalBits stage)

/-- HTFFT uses one rounding policy for generated twiddle coefficients, just
as its butterfly arithmetic does. It is derived rather than configurable. -/
def Configuration.twiddleRounding (_configuration : Configuration depth)
    (_stage : Fin depth) : FixedPoint.RoundingMode :=
  .nearestTiesToEven

/-- Twiddles are generated with substantially more precision than their
stored format.  This is an implementation detail of the certified generator,
not a hardware configuration choice. -/
def Configuration.twiddleGuardBits (_configuration : Configuration depth) :
    Nat :=
  16

@[simp] theorem Configuration.twiddleGuardBits_pos
    (configuration : Configuration depth) :
    0 < configuration.twiddleGuardBits := by
  simp [Configuration.twiddleGuardBits]

/-- The concrete twiddle table owned by this streaming configuration. -/
def Configuration.twiddleTable (configuration : Configuration depth) :
    HTFFT.Fixed.TwiddleTable depth :=
  HTFFT.Fixed.quantizeTwiddleTable
    configuration.arithmetic.twiddleFormat
    configuration.twiddleRounding
    (HTFFT.Fixed.TwiddleGenerator.forFormats
      configuration.arithmetic.twiddleFormat
      configuration.twiddleGuardBits)

/-- The generated rational table underlying the stored integer coefficients. -/
def Configuration.twiddleApproximations
    (configuration : Configuration depth) :
    HTFFT.Fixed.RationalTwiddleTable depth :=
  HTFFT.Fixed.TwiddleGenerator.forFormats
    configuration.arithmetic.twiddleFormat configuration.twiddleGuardBits

/-- Certified pre-quantization error of the generated rational table. -/
noncomputable def Configuration.twiddleGenerationError
    (configuration : Configuration depth) (stage : Fin depth) : ℝ :=
  HTFFT.Fixed.TwiddleGenerator.approximationError
    (HTFFT.Fixed.TwiddleGenerator.workingBits
      configuration.arithmetic.twiddleFormat
      configuration.twiddleGuardBits stage)

theorem Configuration.twiddleGenerationError_le_workingQuantum
    (configuration : Configuration depth) (stage : Fin depth) :
    configuration.twiddleGenerationError stage ≤
      1 / (2 : ℝ) ^ (HTFFT.Fixed.TwiddleGenerator.workingBits
        configuration.arithmetic.twiddleFormat
        configuration.twiddleGuardBits stage) := by
  exact HTFFT.Fixed.TwiddleGenerator.approximationError_le_workingQuantum _

/-- Generation is always at least as accurate as the destination format. -/
theorem Configuration.twiddleGenerationError_le_quantum
    (configuration : Configuration depth) (stage : Fin depth) :
    configuration.twiddleGenerationError stage ≤
      HTFFT.Fixed.quantum (configuration.arithmetic.twiddleFormat stage) := by
  apply configuration.twiddleGenerationError_le_workingQuantum stage |>.trans
  unfold HTFFT.Fixed.quantum
  have bits :
      (configuration.arithmetic.twiddleFormat stage).fractionalBits ≤
        HTFFT.Fixed.TwiddleGenerator.workingBits
          configuration.arithmetic.twiddleFormat
          configuration.twiddleGuardBits stage := by
    simp [HTFFT.Fixed.TwiddleGenerator.workingBits]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) bits

/-- The precision-driven generator automatically encloses the exact roots of
unity; callers do not supply numerical approximations or their proof. -/
theorem Configuration.twiddleEnclosure
    (configuration : Configuration depth) :
    HTFFT.Fixed.TwiddleEnclosure configuration.twiddleApproximations
      configuration.twiddleGenerationError := by
  exact HTFFT.Fixed.TwiddleGenerator.forFormats_enclosure
    configuration.arithmetic.twiddleFormat configuration.twiddleGuardBits

/-- The generated table fits because top-level FFT twiddles always use the
supported signed-Q2 format. -/
theorem Configuration.twiddlesFit (configuration : Configuration depth) :
    HTFFT.Fixed.QuantizedTwiddleFits
      configuration.arithmetic.twiddleFormat
      configuration.twiddleRounding
      configuration.twiddleApproximations := by
  change HTFFT.Fixed.QuantizedTwiddleFits
    (fun stage => HTFFT.Fixed.TwiddleGenerator.q2Format
      (configuration.twiddleFractionalBits stage))
    (fun _ => .nearestTiesToEven)
    (HTFFT.Fixed.TwiddleGenerator.forFormats
      (fun stage => HTFFT.Fixed.TwiddleGenerator.q2Format
        (configuration.twiddleFractionalBits stage))
      configuration.twiddleGuardBits)
  exact HTFFT.Fixed.TwiddleGenerator.generated_q2_fits
    configuration.twiddleFractionalBits
    configuration.twiddleFractionalBits_min
    configuration.twiddleGuardBits (configuration.twiddleGuardBits_pos)

@[simp] theorem Configuration.twiddleTable_value
    (configuration : Configuration depth) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    configuration.twiddleTable.value stage offset =
      FixedPoint.encodeComplex (configuration.twiddleRounding stage)
        (configuration.arithmetic.twiddleFormat stage)
        (configuration.twiddleApproximations.value stage offset) :=
  rfl

/-- End-to-end coefficient error budget supplied by generation followed by
fixed-point quantization. -/
noncomputable def Configuration.twiddleError
    (configuration : Configuration depth) (stage : Fin depth) : ℝ :=
  Real.sqrt 2 * (configuration.twiddleGenerationError stage +
    HTFFT.Fixed.quantum (configuration.arithmetic.twiddleFormat stage))

/-- Complete accuracy certificate for the generated and quantized table. -/
theorem Configuration.twiddleAccuracy
    (configuration : Configuration depth) :
    HTFFT.Fixed.TwiddleAccuracy configuration.arithmetic.fixedConfig
      configuration.twiddleTable configuration.twiddleError := by
  have formats : configuration.arithmetic.fixedConfig.twiddleFormat =
      configuration.arithmetic.twiddleFormat := by
    funext stage
    rfl
  have fits := configuration.twiddlesFit
  unfold Configuration.twiddleTable
  rw [← formats] at fits ⊢
  exact HTFFT.Fixed.twiddleAccuracy_of_enclosure
    configuration.arithmetic.fixedConfig
    configuration.twiddleRounding configuration.twiddleApproximations
    configuration.twiddleGenerationError configuration.twiddleEnclosure
    fits

/-- Hardware-facing representability follows from the generated-table
accuracy certificate. -/
theorem Configuration.storedTwiddlesFit
    (configuration : Configuration depth) :
    configuration.arithmetic.TwiddlesFit configuration.twiddleTable :=
  FFTConfiguration.TwiddlesFit.ofAccuracy configuration.arithmetic
    configuration.twiddleTable configuration.twiddleError
    configuration.twiddleAccuracy

/-- The derived Q2 twiddle formats always leave enough result bits in the
generic complex multiplier. -/
theorem Configuration.productCarriersCover
    (configuration : Configuration depth) :
    configuration.arithmetic.ProductCarriersCover := by
  intro stage
  apply PipelinedFixedButterfly.productCarrierCoversData_of_fractionalBits_le_width
  simp [Configuration.arithmetic, HTFFT.Fixed.TwiddleGenerator.q2Format]

/-- Maximum combined input magnitude/error envelope admitted by all derived
fixed-point formats.  It is computed backwards from the configured output
format, generated-twiddle error, and per-stage rounding error. -/
noncomputable def Configuration.safeInputMagnitude
    (configuration : Configuration depth) : ℝ :=
  HTFFT.Fixed.inputBudget configuration.arithmetic.fixedConfig
    configuration.twiddleError

/-- Magnitude/error envelope at the natural-order FFT output, derived from
the initial envelope and every configured arithmetic stage. -/
noncomputable def Configuration.outputBounds
    (configuration : Configuration depth) (initial : HTFFT.Fixed.Bounds) :
    HTFFT.Fixed.Bounds :=
  HTFFT.Fixed.boundsAt configuration.arithmetic.fixedConfig
    configuration.twiddleError initial (Fin.last depth)

/-- Euclidean output-error bound derived for an initial envelope. -/
noncomputable def Configuration.outputError
    (configuration : Configuration depth) (initial : HTFFT.Fixed.Bounds) : ℝ :=
  (configuration.outputBounds initial).error

/-- A natural bound on the initial decoded envelope supplies the generic
range layer.  No stage-by-stage or configuration-specific capacity proof is
required. -/
theorem Configuration.rangeSafe
    (configuration : Configuration depth) (initial : HTFFT.Fixed.Bounds)
    (initialFits : initial.total ≤ configuration.safeInputMagnitude) :
    HTFFT.Fixed.RangeSafe configuration.arithmetic.fixedConfig
      configuration.twiddleError initial := by
  apply HTFFT.Fixed.rangeSafe_of_inputBudget
    configuration.arithmetic.fixedConfig configuration.twiddleError initial
    configuration.twiddleAccuracy.error_nonnegative
    (by simpa [Configuration.safeInputMagnitude] using initialFits)
  intro stage
  simp [FFTConfiguration.fixedConfig, FFTConfiguration.boundaryFormat,
    HTFFT.Fixed.Config.butterfly,
    HTFFT.Butterfly.Fixed.Config.initial, Configuration.arithmetic,
    HTFFT.Fixed.TwiddleGenerator.q2Format, Nat.add_assoc]

/-- Number of samples carried in one cycle. -/
abbrev Configuration.laneCount (configuration : Configuration depth) : Nat :=
  2 ^ configuration.laneDepth

/-- Number of cycles in one complete transform frame. -/
abbrev Configuration.frameLength (configuration : Configuration depth) : Nat :=
  2 ^ (depth - configuration.laneDepth)

/-- Exact latency of the concrete initial reorder: one frame through the
alternating register banks, one registered bank output, and the two matching
barrel-shifter pipelines. -/
def Configuration.initialReorderLatency
    (configuration : Configuration depth) : Nat :=
  configuration.frameLength + 1 +
    2 * configuration.initialBarrelPipeline.latency

/-- Exact latency of the concrete final reorder. The two-bank schedule starts
reading a frame when its second input half begins, so the first reordered
cycle appears after half a frame. -/
def Configuration.finalReorderLatency
    (configuration : Configuration depth) : Nat :=
  2 ^ (depth - configuration.laneDepth - 1)

@[simp] theorem Configuration.finalReorderLatency_pos
    (configuration : Configuration depth) :
    0 < configuration.finalReorderLatency := by
  simp [Configuration.finalReorderLatency]

@[simp] theorem Configuration.frameLength_pos
    (configuration : Configuration depth) :
    0 < configuration.frameLength := by
  simp [Configuration.frameLength]

theorem Configuration.frame_cardinality
    (configuration : Configuration depth) :
    configuration.frameLength * configuration.laneCount = 2 ^ depth := by
  rw [Configuration.frameLength, Configuration.laneCount, ← Nat.pow_add]
  congr
  exact Nat.sub_add_cancel configuration.laneDepth_le_depth

/-- Boundary after the parallel unrolled prefix has completed. -/
abbrev Configuration.prefixBoundary
    (configuration : Configuration depth) : HTFFT.Exact.LayerBoundary depth :=
  ⟨configuration.laneDepth,
    Nat.lt_succ_of_le configuration.laneDepth_le_depth⟩

/-- Embed a stage of the unrolled prefix into the complete FFT stage index. -/
abbrev Configuration.globalStage (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) : Fin depth :=
  ⟨stage.val, lt_of_lt_of_le stage.isLt configuration.laneDepth_le_depth⟩

/-- Embed a boundary of the unrolled prefix into the complete FFT. -/
abbrev Configuration.globalBoundary (configuration : Configuration depth)
    (boundary : HTFFT.Exact.LayerBoundary configuration.laneDepth) :
    HTFFT.Exact.LayerBoundary depth :=
  ⟨boundary.val, lt_of_lt_of_le boundary.isLt
    (Nat.succ_le_succ configuration.laneDepth_le_depth)⟩

/-- Physical streamed layout consumed by the rolled suffix.  At this boundary
the layout is ordinary cycle-major order. -/
def Configuration.prefixGeometry
    (configuration : Configuration depth) : FFTStage.BoundaryGeometry depth where
  laneDepth := configuration.laneDepth
  completed := configuration.prefixBoundary
  laneDepth_pos := configuration.laneDepth_pos
  laneDepth_le_completed := Nat.le_refl _
  completed_pos := configuration.laneDepth_pos

@[simp] theorem Configuration.prefixGeometry_laneDepth
    (configuration : Configuration depth) :
    configuration.prefixGeometry.laneDepth = configuration.laneDepth :=
  rfl

/-- Physical streamed layout produced after every FFT layer. -/
def Configuration.finalGeometry
    (configuration : Configuration depth) : FFTStage.BoundaryGeometry depth where
  laneDepth := configuration.laneDepth
  completed := Fin.last depth
  laneDepth_pos := configuration.laneDepth_pos
  laneDepth_le_completed := configuration.laneDepth_le_depth
  completed_pos := lt_of_lt_of_le configuration.laneDepth_pos
    configuration.laneDepth_le_depth

/-- Geometry of one rolled layer, indexed from zero at the first layer after
the unrolled prefix. -/
def Configuration.rolledStageGeometry (configuration : Configuration depth)
    (index : Fin (depth - configuration.laneDepth)) :
    FFTStage.Geometry depth where
  laneDepth := configuration.laneDepth
  stage := ⟨configuration.laneDepth + index.val, by
    have indexLt := index.isLt
    have laneLe := configuration.laneDepth_le_depth
    omega⟩
  laneDepth_pos := configuration.laneDepth_pos
  laneDepth_le_stage := Nat.le_add_right _ _

@[simp] theorem Configuration.rolledStageGeometry_stage_val
    (configuration : Configuration depth)
    (index : Fin (depth - configuration.laneDepth)) :
    (configuration.rolledStageGeometry index).stage.val =
      configuration.laneDepth + index.val :=
  rfl

@[simp] theorem Configuration.rolledStageGeometry_laneDepth
    (configuration : Configuration depth)
    (index : Fin (depth - configuration.laneDepth)) :
    (configuration.rolledStageGeometry index).laneDepth =
      configuration.laneDepth :=
  rfl

/-- Exact latency of one concrete rolled stage. -/
def Configuration.rolledStageLatency (configuration : Configuration depth)
    (index : Fin (depth - configuration.laneDepth)) : Nat :=
  FFTStage.latency (configuration.rolledStageGeometry index)
    (configuration.rolledButterflyPipeline index)

/-- Exact latency of the complete concrete rolled suffix. -/
def Configuration.stageChainLatency
    (configuration : Configuration depth) : Nat :=
  ((List.finRange (depth - configuration.laneDepth)).map
    configuration.rolledStageLatency).sum

@[simp] theorem Configuration.finalGeometry_laneDepth
    (configuration : Configuration depth) :
    configuration.finalGeometry.laneDepth = configuration.laneDepth :=
  rfl

@[simp] theorem Configuration.prefixGeometry_laneCount
    (configuration : Configuration depth) :
    configuration.prefixGeometry.laneCount = configuration.laneCount :=
  rfl

@[simp] theorem Configuration.prefixGeometry_completed
    (configuration : Configuration depth) :
    configuration.prefixGeometry.completed =
      configuration.prefixBoundary :=
  rfl

@[simp] theorem Configuration.prefixGeometry_frameLength
    (configuration : Configuration depth) :
    configuration.prefixGeometry.frameLength = configuration.frameLength :=
  rfl

@[simp] theorem Configuration.finalGeometry_laneCount
    (configuration : Configuration depth) :
    configuration.finalGeometry.laneCount = configuration.laneCount :=
  rfl

@[simp] theorem Configuration.finalGeometry_completed
    (configuration : Configuration depth) :
    configuration.finalGeometry.completed = Fin.last depth :=
  rfl

@[simp] theorem Configuration.finalGeometry_frameLength
    (configuration : Configuration depth) :
    configuration.finalGeometry.frameLength = configuration.frameLength :=
  rfl

/-- The unrolled-network configuration induced for the parallel prefix. -/
abbrev Configuration.unrolled
    (configuration : Configuration depth) : UnrolledFFT.Configuration configuration.laneDepth where
  inputFormat := configuration.arithmetic.inputFormat
  twiddleFormat stage :=
    configuration.arithmetic.twiddleFormat
      ⟨stage.val, lt_of_lt_of_le stage.isLt configuration.laneDepth_le_depth⟩
  butterflyPipeline := configuration.unrolledButterflyPipeline
  boundaryLatency := configuration.unrolledBoundaryLatency

/-- Restrict the configuration-owned twiddle table to the unrolled prefix. -/
def Configuration.prefixTable (configuration : Configuration depth) :
    HTFFT.Fixed.TwiddleTable configuration.laneDepth where
  value stage :=
    configuration.twiddleTable.value (configuration.globalStage stage)

@[simp] theorem Configuration.globalBoundary_final
    (configuration : Configuration depth) :
    configuration.globalBoundary (Fin.last configuration.laneDepth) =
      configuration.prefixBoundary := by
  apply Fin.ext
  rfl

@[simp] theorem Configuration.unrolled_boundaryFormat
    (configuration : Configuration depth)
    (boundary : HTFFT.Exact.LayerBoundary configuration.laneDepth) :
    configuration.unrolled.fixedConfig.boundaryFormat boundary =
      configuration.arithmetic.fixedConfig.boundaryFormat
        (configuration.globalBoundary boundary) := by
  rfl

@[simp] theorem Configuration.unrolled_twiddleFormat
    (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) :
    configuration.unrolled.fixedConfig.twiddleFormat stage =
      configuration.arithmetic.fixedConfig.twiddleFormat
        (configuration.globalStage stage) := by
  rfl

@[simp] theorem Configuration.unrolled_productFormat
    (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) :
    configuration.unrolled.fixedConfig.productFormat stage =
      configuration.arithmetic.fixedConfig.productFormat
        (configuration.globalStage stage) := by
  rfl

@[simp] theorem Configuration.unrolled_rounding
    (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) :
    configuration.unrolled.fixedConfig.rounding stage =
      configuration.arithmetic.fixedConfig.rounding
        (configuration.globalStage stage) := by
  rfl

/-- Full-table twiddle representability restricts to the unrolled prefix. -/
theorem Configuration.unrolledTwiddlesFit
    (configuration : Configuration depth)
    (fits : configuration.arithmetic.TwiddlesFit
      configuration.twiddleTable) :
    configuration.unrolled.TwiddlesFit
      configuration.prefixTable := by
  intro stage offset
  exact fits (configuration.globalStage stage) offset

/-- Full-network product-carrier coverage restricts to the unrolled prefix. -/
theorem Configuration.unrolledProductCarriersCover
    (configuration : Configuration depth)
    (covers : configuration.arithmetic.ProductCarriersCover) :
    configuration.unrolled.ProductCarriersCover := by
  intro stage
  exact covers (configuration.globalStage stage)

/-- End-to-end latency once the four functional transforms are connected.
Marker alignment across the unrolled prefix is accounted for separately by
the structural shell. -/
def Configuration.totalLatency
    (configuration : Configuration depth) : Nat :=
  configuration.initialReorderLatency +
    configuration.unrolled.networkLatency +
    configuration.stageChainLatency +
    configuration.finalReorderLatency

end HTFFT.Silean.FFT
