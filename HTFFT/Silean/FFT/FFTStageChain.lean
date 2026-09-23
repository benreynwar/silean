import HTFFT.Silean.FFT.Frame
import Silean.Authoring.ModulePorts

/-! # Rolled FFT-stage chain interface

This module specifies the whole rolled suffix as one framed transformation.
Its contract says only which pure fixed-point layers are applied and how the
physical frame layouts are interpreted; individual stage implementations are
deliberately absent.
-/

namespace HTFFT.Silean.FFT.FFTStageChain

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
    (index : StageIndex configuration) : FFTStage.Geometry depth where
  laneDepth := configuration.laneDepth
  stage := ⟨configuration.laneDepth + index.val, by
    have indexLt : index.val < depth - configuration.laneDepth := by
      exact index.isLt
    have laneLe := configuration.laneDepth_le_depth
    omega⟩
  laneDepth_pos := configuration.laneDepth_pos
  laneDepth_le_stage := Nat.le_add_right _ _

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
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : PrefixFrame configuration) : HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.layeredSuffix configuration.arithmetic.fixedConfig table
    configuration.prefixBoundary (decodePrefix configuration input)

/-- Physical result frame at the final streamed boundary. -/
def resultFrame (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : PrefixFrame configuration) : OutputFrame configuration :=
  encodeFinalPhysical configuration (resultValue configuration table input)

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

def contract (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  FramedLatency.Holds configuration.frameLength
    configuration.stageChainLatency configuration.frameLength_pos
    (fun input => (inputObservation configuration input).1 = true)
    (fun output => (outputObservation configuration output).1 = true)
    (frameRelation configuration table) trace

theorem relates_of_contract (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    {trace : BoundaryTrace (ports configuration)}
    (holds : contract configuration table trace) :
    FramedLatency.Relates configuration.frameLength
      configuration.stageChainLatency configuration.frameLength_pos
      (fun input : InputObservation configuration => input.1 = true)
      (fun output : OutputObservation configuration => output.1 = true)
      (carriedRelation configuration table)
      (trace.inputs.map (inputObservation configuration))
      (trace.outputs.map (outputObservation configuration)) :=
  FramedLatency.relates_of_holds_projection
    (inputObservation configuration) (outputObservation configuration) holds

end HTFFT.Silean.FFT.FFTStageChain
