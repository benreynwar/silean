import HTFFT.Silean.FFTStage.FFTStage
import HTFFT.Silean.UnrolledFFT.Configuration
import HTFFT.Fixed.TwiddleTable
import Silean.Modules.BarrelShifter.BarrelShifter

/-! # Complete streamed FFT configuration

The complete FFT has `2 ^ depth` samples and carries `2 ^ laneDepth` samples
per cycle. Numeric formats are shared by the unrolled prefix and rolled
suffix. Pipeline placements and frame-storage latencies are explicit static
choices; the rolled-chain latency is derived from its concrete stages.
-/

namespace HTFFT.Silean.FFT

/-- Static choices for the complete mixed unrolled/streamed FFT. -/
structure Configuration (depth : Nat) where
  arithmetic : FFTConfiguration depth
  /-- Rational coefficient approximations from which the concrete stored
  twiddle table is generated. -/
  twiddleApproximations : HTFFT.Fixed.RationalTwiddleTable depth
  /-- Quantization policy used to turn each stage's rational approximations
  into the concrete stored twiddle values. -/
  twiddleRounding : Fin depth → FixedPoint.RoundingMode
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

/-- The concrete twiddle table owned by this streaming configuration. -/
def Configuration.twiddleTable (configuration : Configuration depth) :
    HTFFT.Fixed.TwiddleTable depth :=
  HTFFT.Fixed.quantizeTwiddleTable
    configuration.arithmetic.twiddleFormat
    configuration.twiddleRounding
    configuration.twiddleApproximations

@[simp] theorem Configuration.twiddleTable_value
    (configuration : Configuration depth) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    configuration.twiddleTable.value stage offset =
      FixedPoint.encodeComplex (configuration.twiddleRounding stage)
        (configuration.arithmetic.twiddleFormat stage)
        (configuration.twiddleApproximations.value stage offset) :=
  rfl

/-- Promote certified rational approximations owned by the configuration to
an accuracy certificate for its generated stored table. -/
theorem Configuration.twiddleAccuracy_of_enclosure
    (configuration : Configuration depth)
    (approximationError : Fin depth → ℝ)
    (enclosure : HTFFT.Fixed.TwiddleEnclosure
      configuration.twiddleApproximations approximationError)
    (fits : HTFFT.Fixed.QuantizedTwiddleFits
      configuration.arithmetic.twiddleFormat
      configuration.twiddleRounding
      configuration.twiddleApproximations) :
    HTFFT.Fixed.TwiddleAccuracy configuration.arithmetic.fixedConfig
      configuration.twiddleTable
      (fun stage => Real.sqrt 2 *
        (approximationError stage + HTFFT.Fixed.quantum
          (configuration.arithmetic.twiddleFormat stage))) := by
  have formats : configuration.arithmetic.fixedConfig.twiddleFormat =
      configuration.arithmetic.twiddleFormat := by
    funext stage
    rfl
  unfold Configuration.twiddleTable
  rw [← formats] at fits ⊢
  exact HTFFT.Fixed.twiddleAccuracy_of_enclosure
    configuration.arithmetic.fixedConfig
    configuration.twiddleRounding
    configuration.twiddleApproximations approximationError enclosure fits

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
