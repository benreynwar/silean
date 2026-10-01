import HTFFT.Silean.FFT.Frame
import Silean.Authoring.ModulePorts

/-! # Rolled FFT-stage chain interface

This module specifies the whole rolled suffix as one framed transformation.
Its contract says only which pure fixed-point layers are applied and how the
physical frame layouts are interpreted; individual stage implementations are
deliberately absent.
-/

namespace HTFFT.Silean.FFTStageChain
open FFT

open _root_.Silean

/-- Number of rolled layers following the lane-local unrolled prefix. -/
abbrev stageCount (depth : Nat) (configuration : Configuration depth) :=
  depth - configuration.laneDepth

/-- Indices of the rolled layers following the lane-local unrolled prefix. -/
abbrev StageIndex (configuration : Configuration depth) :=
  Fin (stageCount depth configuration)

/-- Geometry of one rolled layer, indexed from zero at the first layer after
the unrolled prefix. -/
def stageGeometry (configuration : Configuration depth)
    (index : StageIndex configuration) : FFTStage.Geometry depth :=
  configuration.rolledStageGeometry index

@[simp] theorem stageGeometry_stage_val
    (configuration : Configuration depth)
    (index : StageIndex configuration) :
    (stageGeometry configuration index).stage.val =
      configuration.laneDepth + index.val :=
  rfl

@[simp] theorem stageGeometry_frameLength
    (configuration : Configuration depth)
    (index : StageIndex configuration) :
    (stageGeometry configuration index).frameLength =
      configuration.frameLength :=
  rfl

@[simp] theorem stageGeometry_laneCount
    (configuration : Configuration depth)
    (index : StageIndex configuration) :
    (stageGeometry configuration index).laneCount =
      configuration.laneCount :=
  rfl

/-- Total latency contributed by a proposed latency for every rolled stage. -/
def accumulatedLatency (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat) : Nat :=
  ((List.finRange (stageCount depth configuration)).map stageLatency).sum

/-- Pure fixed-point suffix result carried by the chain. -/
def resultValue (configuration : Configuration depth)
    (input : PrefixFrame configuration) : HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.layeredSuffix configuration.arithmetic.fixedConfig
    configuration.twiddleTable
    configuration.prefixBoundary (decodePrefix configuration input)

/-- Physical result frame at the final streamed boundary. -/
def resultFrame (configuration : Configuration depth)
    (input : PrefixFrame configuration) : OutputFrame configuration :=
  encodeFinalPhysical configuration (resultValue configuration input)

module_ports ports (configuration : Configuration depth) where
  input i_first : .bit,
  input i_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat configuration.prefixBoundary)),
  output o_first : .bit,
  output o_data : .vector configuration.laneCount
    (UnrolledFFTLayer.complexSignalType
      (configuration.arithmetic.boundaryFormat (Fin.last depth)))

abbrev InputObservation (configuration : Configuration depth) :=
  Bool × PrefixData configuration

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
    configuration.stageChainLatency configuration.frameLength_pos
    (fun input => (inputObservation configuration input).1 = true)
    (fun output => (outputObservation configuration output).1 = true)
    (frameRelation configuration) trace

theorem relates_of_contract (configuration : Configuration depth)
    {trace : BoundaryTrace (ports configuration)}
    (holds : contract configuration trace) :
    FramedLatency.Relates configuration.frameLength
      configuration.stageChainLatency configuration.frameLength_pos
      (fun input : InputObservation configuration => input.1 = true)
      (fun output : OutputObservation configuration => output.1 = true)
      (carriedRelation configuration)
      (trace.inputs.map (inputObservation configuration))
      (trace.outputs.map (outputObservation configuration)) :=
  FramedLatency.relates_of_holds_projection
    (inputObservation configuration) (outputObservation configuration) holds

end HTFFT.Silean.FFTStageChain
