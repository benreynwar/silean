import HTFFT.Silean.FFT.Frame
import Silean.Authoring.ModulePorts

/-! # Initial streamed-frame reorder

The initial reorder converts a naturally ordered input frame into the complete
bit-reversed order consumed by the ascending unrolled butterfly network.  It
changes only where packed samples occur; it performs no arithmetic.
-/

namespace HTFFT.Silean.FFT.InitialReorder

open _root_.Silean

/-- Reorder one natural input frame into the complete global bit-reversed order
consumed by the unrolled prefix network. -/
def resultFrame (configuration : Configuration depth)
    (input : InputFrame configuration) : InputFrame configuration :=
  fun cycle lane =>
    HTFFT.Exact.bitReverse (unpackInput configuration input)
      (naturalLayout configuration (cycle, lane))

module_ports ports (configuration : Configuration depth) where
  input i_first : .bit,
  input i_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat 0)),
  output o_first : .bit,
  output o_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat 0))

abbrev InputObservation (configuration : Configuration depth) :=
  Bool × InputData configuration

abbrev OutputObservation (configuration : Configuration depth) :=
  Bool × InputData configuration

def inputObservation (configuration : Configuration depth)
    (input : (ports configuration).inputs.Values) :
    InputObservation configuration :=
  (input Input.i_first, input Input.i_data)

def outputObservation (configuration : Configuration depth)
    (output : (ports configuration).outputs.Values) :
    OutputObservation configuration :=
  (output Output.o_first, output Output.o_data)

/-- Natural carried relation: the marker is handled by `FramedLatency`, while
the complete packed payload is permuted by `resultFrame`. -/
def carriedRelation (configuration : Configuration depth)
    (input : FramedLatency.Frame configuration.frameLength
      (InputObservation configuration))
    (output : FramedLatency.Frame configuration.frameLength
      (OutputObservation configuration)) : Prop :=
  (fun cycle => (output cycle).2) =
    resultFrame configuration (fun cycle => (input cycle).2)

def frameRelation (configuration : Configuration depth)
    (input : FramedLatency.Frame configuration.frameLength
      (ports configuration).inputs.Values)
    (output : FramedLatency.Frame configuration.frameLength
      (ports configuration).outputs.Values) : Prop :=
  carriedRelation configuration
    (fun cycle => inputObservation configuration (input cycle))
    (fun cycle => outputObservation configuration (output cycle))

/-- Every well-formed input frame is reordered after the configured latency,
with its frame marker kept aligned to the reordered payload. -/
def contract (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  FramedLatency.Holds configuration.frameLength
    configuration.initialReorderLatency configuration.frameLength_pos
    (fun input => (inputObservation configuration input).1 = true)
    (fun output => (outputObservation configuration output).1 = true)
    (frameRelation configuration) trace

theorem relates_of_contract (configuration : Configuration depth)
    {trace : BoundaryTrace (ports configuration)}
    (holds : contract configuration trace) :
    FramedLatency.Relates configuration.frameLength
      configuration.initialReorderLatency configuration.frameLength_pos
      (fun input : InputObservation configuration => input.1 = true)
      (fun output : OutputObservation configuration => output.1 = true)
      (carriedRelation configuration)
      (trace.inputs.map (inputObservation configuration))
      (trace.outputs.map (outputObservation configuration)) :=
  FramedLatency.relates_of_holds_projection
    (inputObservation configuration) (outputObservation configuration) holds

end HTFFT.Silean.FFT.InitialReorder
