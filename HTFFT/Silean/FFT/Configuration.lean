import HTFFT.Silean.FFTStage.FrameLayout
import HTFFT.Silean.UnrolledFFT.Configuration

/-! # Complete streamed FFT configuration

The complete FFT has `2 ^ depth` samples and carries `2 ^ laneDepth` samples
per cycle.  Numeric formats are shared by the unrolled prefix and rolled
suffix.  Pipeline and frame-storage latencies remain explicit static choices.
-/

namespace HTFFT.Silean.FFT

/-- Static choices for the complete mixed unrolled/streamed FFT. -/
structure Configuration (depth : Nat) where
  arithmetic : FFTConfiguration depth
  laneDepth : Nat
  laneDepth_pos : 0 < laneDepth
  laneDepth_le_depth : laneDepth ≤ depth
  unrolledButterflyPipeline : Fin laneDepth →
    PipelinedFixedButterfly.Pipeline
  unrolledBoundaryLatency : HTFFT.Exact.LayerBoundary laneDepth → Nat
  initialReorderLatency : Nat
  stageChainLatency : Nat
  finalReorderLatency : Nat

/-- Number of samples carried in one cycle. -/
abbrev Configuration.laneCount (configuration : Configuration depth) : Nat :=
  2 ^ configuration.laneDepth

/-- Number of cycles in one complete transform frame. -/
abbrev Configuration.frameLength (configuration : Configuration depth) : Nat :=
  2 ^ (depth - configuration.laneDepth)

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

/-- Restrict the complete twiddle table to the unrolled prefix. -/
def Configuration.prefixTable (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    HTFFT.Fixed.TwiddleTable configuration.laneDepth where
  value stage :=
    table.value (configuration.globalStage stage)

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
