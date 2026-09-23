import HTFFT.Silean.FFT.FFT
import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetworkDerived
import Silean.Authoring.ModuleDesign
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived

/-! Permanent top-level FFT body with unresolved functional children. -/

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FFT
    (depth : Nat) (configuration : FFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) where
  boundary (FFT.ports configuration)
    (naming := FFT.Naming.ports configuration)
  instances {
    initialReorder := unresolved (FFT.InitialReorder.ports configuration),
    unrolled := UnrolledFFTNetwork.design configuration.laneDepth
      configuration.unrolled (configuration.prefixTable table),
    unrolledFirstDelay := OptionalShiftRegister.design .bit
      configuration.unrolled.networkLatency,
    stageChain := unresolved (FFT.FFTStageChain.ports configuration),
    finalReorder := unresolved (FFT.FinalReorder.ports configuration) }
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
