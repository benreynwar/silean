import HTFFT.Silean.FFT.FFT
import HTFFT.Silean.InitialReorder.InitialReorderDerived
import HTFFT.Silean.FFTStageChain.FFTStageChainDerived
import HTFFT.Silean.FinalReorder.FinalReorderDerived
import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetworkDerived
import Silean.Authoring.ModuleDesign
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived

/-! Concrete top-level FFT hierarchy. -/

namespace HTFFT.Silean.FFT.Internal

/-- Stable emission identity for every structural choice in the complete FFT.
The child specializations remain the authoritative encodings of their own
numeric and pipeline parameters. -/
def specialization (configuration : Configuration depth) :
    List _root_.Silean.Naming.ModuleParameter :=
  InitialReorder.Internal.specialization configuration ++
  UnrolledFFTNetwork.Internal.specialization configuration.unrolled
    configuration.prefixTable ++
  FFTStageChain.Internal.specialization configuration ++
  FinalReorder.Internal.specialization configuration

/-- The rolled ROM definition names supply the non-numeric part of the
complete hierarchy's emission identity. -/
def variant (configuration : Configuration depth) : String :=
  FFTStageChain.Internal.variant configuration

end HTFFT.Silean.FFT.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FFT
    (depth : Nat) (configuration : FFT.Configuration depth)
    (variant := FFT.Internal.variant configuration)
    (specialization := FFT.Internal.specialization configuration) where
  boundary (FFT.ports configuration)
    (naming := FFT.Naming.ports configuration)
  instances {
    initialReorder := InitialReorder.design depth configuration,
    unrolled := UnrolledFFTNetwork.design configuration.laneDepth
      configuration.unrolled configuration.prefixTable,
    unrolledFirstDelay := OptionalShiftRegister.design .bit
      configuration.unrolled.networkLatency,
    stageChain := FFTStageChain.design depth configuration,
    finalReorder := FinalReorder.design depth configuration }
  wiring {
    outputs {
      .o_first := finalReorder.o_first,
      .o_data := finalReorder.o_data }
    instance (.initialReorder) {
      .i_first := input.i_first,
      .i_data := input.i_data }
    instance (.unrolled) {
      .input := initialReorder.o_data }
    instance (.unrolledFirstDelay) {
      .input := initialReorder.o_first }
    instance (.stageChain) {
      .i_first := unrolledFirstDelay.output,
      .i_data := unrolled.output }
    instance (.finalReorder) {
      .i_first := stageChain.o_first,
      .i_data := stageChain.o_data }
  }

end HTFFT.Silean
