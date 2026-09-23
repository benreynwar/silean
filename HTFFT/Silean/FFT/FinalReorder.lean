import HTFFT.Silean.FFT.Frame
import Silean.Authoring.ModulePorts

/-! # Final streamed-frame reorder

The rolled suffix emits its result in the last stage's efficient physical
layout.  The final reorder converts that frame to ordinary natural-frequency
cycle-major order without changing any packed sample.
-/

namespace HTFFT.Silean.FFT.FinalReorder

open _root_.Silean

def resultFrame (configuration : Configuration depth)
    (input : OutputFrame configuration) : OutputFrame configuration :=
  packOutput configuration (unpackFinalPhysical configuration input)

module_ports ports (configuration : Configuration depth) where
  input i_first : .bit,
  input i_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat (Fin.last depth))),
  output o_first : .bit,
  output o_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat (Fin.last depth)))

abbrev InputObservation (configuration : Configuration depth) :=
  Bool × OutputData configuration

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

def contract (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  FramedLatency.Holds configuration.frameLength
    configuration.finalReorderLatency configuration.frameLength_pos
    (fun input => (inputObservation configuration input).1 = true)
    (fun output => (outputObservation configuration output).1 = true)
    (frameRelation configuration) trace

theorem relates_of_contract (configuration : Configuration depth)
    {trace : BoundaryTrace (ports configuration)}
    (holds : contract configuration trace) :
    FramedLatency.Relates configuration.frameLength
      configuration.finalReorderLatency configuration.frameLength_pos
      (fun input : InputObservation configuration => input.1 = true)
      (fun output : OutputObservation configuration => output.1 = true)
      (carriedRelation configuration)
      (trace.inputs.map (inputObservation configuration))
      (trace.outputs.map (outputObservation configuration)) :=
  FramedLatency.relates_of_holds_projection
    (inputObservation configuration) (outputObservation configuration) holds

end HTFFT.Silean.FFT.FinalReorder
