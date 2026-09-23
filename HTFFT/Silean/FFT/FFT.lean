import HTFFT.Silean.FFT.InitialReorder
import HTFFT.Silean.FFT.FFTStageChain
import HTFFT.Silean.FFT.FinalReorder

/-! # Complete streamed fixed-point FFT

The public contract interprets a naturally ordered input frame, applies the
ordinary pure fixed-point FFT, and returns the result in natural-frequency
order after one explicit total latency.  It does not mention reorder storage,
the unrolled prefix, rolled stages, or structural state.
-/

namespace HTFFT.Silean.FFT

open _root_.Silean

/-- Natural mathematical result of one complete input frame. -/
def resultValue (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration) : HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.layeredFFT configuration.arithmetic.fixedConfig table
    (decodeInput configuration input)

/-- Packed natural-frequency output frame. -/
def resultFrame (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration) : OutputFrame configuration :=
  encodeOutput configuration (resultValue configuration table input)

module_ports ports (configuration : Configuration depth) where
  input i_first : .bit,
  input i_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat 0)),
  output o_first : .bit,
  output o_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat (Fin.last depth)))

abbrev InputObservation (configuration : Configuration depth) :=
  Bool × InputData configuration

abbrev OutputObservation (configuration : Configuration depth) :=
  Bool × OutputData configuration

def inputObservation (configuration : Configuration depth)
    (input : (ports configuration).inputs.Values) :
    InputObservation configuration :=
  (input Input.i_first, input Input.i_data)

def outputObservation (configuration : Configuration depth)
    (output : (ports configuration).outputs.Values) :
    OutputObservation configuration :=
  (output Output.o_first, output Output.o_data)

def carriedRelation (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : FramedLatency.Frame configuration.frameLength
      (InputObservation configuration))
    (output : FramedLatency.Frame configuration.frameLength
      (OutputObservation configuration)) : Prop :=
  (fun cycle => (output cycle).2) =
    resultFrame configuration table (fun cycle => (input cycle).2)

def frameRelation (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : FramedLatency.Frame configuration.frameLength
      (ports configuration).inputs.Values)
    (output : FramedLatency.Frame configuration.frameLength
      (ports configuration).outputs.Values) : Prop :=
  carriedRelation configuration table
    (fun cycle => inputObservation configuration (input cycle))
    (fun cycle => outputObservation configuration (output cycle))

/-- Complete framed FFT contract.

Only a full frame beginning with `i_first` and containing no later `i_first`
constrains an output.  Its natural-order fixed-point FFT appears after
`totalLatency`, with `o_first` aligned to the first output cycle. -/
def contract (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  FramedLatency.Holds configuration.frameLength
    configuration.totalLatency configuration.frameLength_pos
    (fun input => (inputObservation configuration input).1 = true)
    (fun output => (outputObservation configuration output).1 = true)
    (frameRelation configuration table) trace

end HTFFT.Silean.FFT
