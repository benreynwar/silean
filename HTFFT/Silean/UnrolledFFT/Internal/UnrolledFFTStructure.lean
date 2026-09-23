import HTFFT.Silean.UnrolledFFT.UnrolledFFT
import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetworkDerived
import Silean.Authoring.ModuleDesign
import Silean.Modules.VectorReindex.VectorReindexDerived

/-! Static bit-reversal wrapper around the ascending unrolled network. -/

namespace HTFFT.Silean.UnrolledFFT.Internal

open _root_.Silean

/-- Stable emission identity for the natural-order wrapper. -/
def specialization (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    List _root_.Silean.Naming.ModuleParameter :=
  UnrolledFFTNetwork.Internal.specialization configuration table

end HTFFT.Silean.UnrolledFFT.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design UnrolledFFT
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (specialization := UnrolledFFT.Internal.specialization configuration table) where
  boundary (UnrolledFFT.ports configuration)
    (naming := UnrolledFFT.Naming.ports configuration)
  instances {
    reorder := VectorReindex.design
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0))
      (2 ^ depth) (2 ^ depth) HTFFT.Exact.bitReverseIndex,
    network := UnrolledFFTNetwork.design depth configuration table }
  wiring {
    outputs {
      .output := network.output }
    instance (.reorder) {
      .input := input.input }
    instance (.network) {
      .input := reorder.output }
  }

end HTFFT.Silean
