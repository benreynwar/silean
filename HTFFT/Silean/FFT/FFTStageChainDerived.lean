import HTFFT.Silean.FFT.Internal.FFTStageChainVerification

/-! Public conditional correctness theorem for the rolled-stage chain body. -/

namespace HTFFT.Silean.FFT.FFTStageChain

open _root_.Silean

/-- The permanent rolled-stage body satisfies the natural chain contract when
every unresolved stage satisfies its public boundary-trace contract and the
stage latencies sum to the latency declared by the chain configuration. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (latencyMatches :
      accumulatedLatency configuration stageLatency =
        configuration.stageChainLatency)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic table
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index))) :
    contract configuration table trace.parent :=
  Internal.contract_of_body_trace configuration table stageLatency trace
    wiring latencyMatches stageCorrect

end HTFFT.Silean.FFT.FFTStageChain
