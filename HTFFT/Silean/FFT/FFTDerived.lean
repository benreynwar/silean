import HTFFT.Silean.FFT.Internal.FFTVerification

/-! Public conditional correctness theorem for the top-level FFT body. -/

namespace HTFFT.Silean.FFT

open _root_.Silean
open _root_.Silean.Modules

/-- The permanent top-level body satisfies the natural FFT contract whenever
its functional children and separate marker shift register satisfy their
public boundary-trace contracts. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (initialCorrect : InitialReorder.contract configuration
      (trace.child .initialReorder))
    (unrolledCorrect : UnrolledFFTNetwork.contract configuration.unrolled
      (configuration.prefixTable table) (trace.child .unrolled))
    (markerDelayCorrect : OptionalShiftRegister.contract .bit
      configuration.unrolled.networkLatency
      (trace.child .unrolledFirstDelay))
    (stageChainCorrect : FFTStageChain.contract configuration table
      (trace.child .stageChain))
    (finalCorrect : FinalReorder.contract configuration
      (trace.child .finalReorder)) :
    contract configuration table trace.parent :=
  Internal.contract_of_body_trace configuration table trace wiring
    initialCorrect unrolledCorrect markerDelayCorrect stageChainCorrect
    finalCorrect

end HTFFT.Silean.FFT
