import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetwork
import Silean.Authoring.ModulePorts
import Silean.Semantics.FixedLatency

/-! # Natural-order unrolled FFT

The public wrapper adds the static input bit reversal required by the
ascending iterative radix-two network.  Its contract is therefore the pure
fixed-point `layeredFFT`, with no hardware indexing details exposed.
-/

namespace HTFFT.Silean.UnrolledFFT

open _root_.Silean

/-- Natural fixed-point result of the complete unrolled FFT. -/
def resultValue (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.layeredFFT configuration.fixedConfig table
    (UnrolledFFTLayer.decodeVector
      (configuration.boundaryFormat 0) input)

module_ports ports (configuration : Configuration depth) where
  input input : .vector (2 ^ depth)
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat 0)),
  output output : .vector (2 ^ depth)
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat (Fin.last depth)))

/-- Every available output is the encoded pure fixed-point FFT of the
corresponding natural-order input. -/
def contract (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  FixedLatency.Holds configuration.networkLatency
    (fun
      (input : (ports configuration).inputs.Values)
      (output : (ports configuration).outputs.Values) =>
      output .output =
        UnrolledFFTLayer.encodeVector
          (configuration.boundaryFormat (Fin.last depth))
          (resultValue configuration table (input .input)))
    trace

end HTFFT.Silean.UnrolledFFT
