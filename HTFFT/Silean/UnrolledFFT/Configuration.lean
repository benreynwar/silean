import HTFFT.Silean.FFTConfiguration

/-! # Unrolled FFT hardware configuration

The shared `FFTConfiguration` owns the numeric policy.  This extension contains
only pipeline-placement choices for the fully unrolled implementation.
-/

namespace HTFFT.Silean.UnrolledFFT

/-- Pipeline choices for a power-of-two unrolled FFT, together with the shared
FFT numeric configuration. -/
structure Configuration (depth : Nat) extends FFTConfiguration depth where
  butterflyPipeline : Fin depth →
    PipelinedFixedButterfly.Pipeline
  /-- Additional synchronized delay at every network boundary, including the
  input and output boundaries.  An internal boundary is an inter-layer delay. -/
  boundaryLatency : HTFFT.Exact.LayerBoundary depth → Nat

/-- Latency of the butterfly bank at one layer. -/
def Configuration.layerLatency (configuration : Configuration depth)
    (stage : Fin depth) : Nat :=
  (configuration.butterflyPipeline stage).latency

/-- Accumulated latency after an explicitly ordered sequence of layers.  The
input-boundary delay occurs first; each layer is followed by the delay at its
output boundary. -/
def Configuration.latencyThrough
    (configuration : Configuration depth) (stages : List (Fin depth)) : Nat :=
  stages.foldl (fun latency stage =>
    latency + configuration.layerLatency stage +
      configuration.boundaryLatency stage.succ)
    (configuration.boundaryLatency 0)

/-- Accumulated latency from the network input through a selected layer
boundary. -/
def Configuration.latencyTo (configuration : Configuration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) : Nat :=
  configuration.latencyThrough
    (HTFFT.Exact.butterflyStagePrefix depth boundary)

/-- End-to-end latency of the complete ascending unrolled network. -/
def Configuration.networkLatency
    (configuration : Configuration depth) : Nat :=
  configuration.latencyThrough (HTFFT.Exact.butterflyStages depth)

@[simp] theorem Configuration.latencyTo_zero
    (configuration : Configuration depth) :
    configuration.latencyTo 0 = configuration.boundaryLatency 0 := by
  simp [Configuration.latencyTo, Configuration.latencyThrough,
    HTFFT.Exact.butterflyStagePrefix]

/-- Advancing one layer adds that layer's latency and the delay at its output
boundary. -/
theorem Configuration.latencyTo_succ
    (configuration : Configuration depth) (stage : Fin depth) :
    configuration.latencyTo stage.succ =
      configuration.latencyTo stage.castSucc +
        configuration.layerLatency stage +
        configuration.boundaryLatency stage.succ := by
  rw [Configuration.latencyTo, Configuration.latencyTo,
    HTFFT.Exact.butterflyStagePrefix_boundarySucc]
  simp [Configuration.latencyThrough, List.foldl_append]

@[simp] theorem Configuration.latencyTo_final
    (configuration : Configuration depth) :
    configuration.latencyTo (Fin.last depth) =
      configuration.networkLatency := by
  unfold Configuration.latencyTo Configuration.networkLatency
    HTFFT.Exact.butterflyStagePrefix HTFFT.Exact.butterflyStages
  have stages : List.take (Fin.last depth).val (List.finRange depth) =
      List.finRange depth := by
    change List.take depth (List.finRange depth) = List.finRange depth
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange depth))
  rw [stages]

end HTFFT.Silean.UnrolledFFT
