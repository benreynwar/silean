import HTFFT.Silean.UnrolledFFTLayer.UnrolledFFTLayer
import Silean.Authoring.ModulePorts
import Silean.Semantics.FixedLatency

/-! # Generic unrolled FFT network

This module composes every ascending fixed-point butterfly layer.  Its input
is already in bit-reversed order; the public `UnrolledFFT` wrapper supplies the
static input permutation needed by a natural-order FFT interface.

Synchronized whole-vector delays may be placed at every layer boundary.  They
affect latency only and do not appear in the mathematical result.
-/

namespace HTFFT.Silean.UnrolledFFTNetwork

open _root_.Silean

/-- Pure vector result of all ascending layers, starting from an already
bit-reversed input vector. -/
def resultValue (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.applyButterflyLayers configuration.fixedConfig table
    (HTFFT.Exact.butterflyStages depth)
    (UnrolledFFTLayer.decodeVector
      (configuration.boundaryFormat 0) input)

module_ports ports (configuration : UnrolledFFT.Configuration depth) where
  input input : .vector (2 ^ depth)
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat 0)),
  output output : .vector (2 ^ depth)
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat (Fin.last depth)))

/-- Every available network output is the encoded result of all ascending
fixed-point layers applied to its corresponding already-reordered input. -/
def contract (configuration : UnrolledFFT.Configuration depth)
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

end HTFFT.Silean.UnrolledFFTNetwork
