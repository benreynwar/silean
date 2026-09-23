import HTFFT.Silean.FFT.Internal.FFTStageChainStructure
import Silean.Semantics.ModuleBodyTrace

/-! Observable wiring equations for the unresolved rolled-stage chain body. -/

namespace HTFFT.Silean.FFT.FFTStageChain.Internal

open _root_.Silean

/-- Transport the payload of an ordinary observation while leaving its frame
marker definitionally unchanged. -/
def castObservation {α β : Type} (equal : α = β)
    (value : Bool × α) : Bool × β :=
  (value.1, equal ▸ value.2)

/-- Transport across an observation-type equality leaves the frame marker
unchanged. -/
@[simp] theorem castObservation_fst {α β : Type}
    (equal : α = β) (value : Bool × α) :
    (castObservation equal value).1 = value.1 := by
  rfl

private theorem pair_cast_eq_castObservation
    {sourceType targetType : SignalType}
    (signalEqual : sourceType = targetType)
    (dataEqual : sourceType.Denote = targetType.Denote)
    (marker : Bool) (value : sourceType.Denote) :
    (marker, signalEqual ▸ value) =
      castObservation dataEqual (marker, value) := by
  cases signalEqual
  have equalProof : dataEqual = rfl := Subsingleton.elim _ _
  rw [equalProof]
  rfl

/-- The first rolled stage observes the parent input. -/
theorem stageInputObservation_of_wiring_zero
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (step : (FFTStageChain.body depth configuration table).Step)
    (wiring : step.WiringHolds)
    (index : StageIndex configuration) (zero : index.val = 0) :
    FFTStage.inputObservation configuration.arithmetic
        (stageGeometry configuration index)
        (step.child (.stage index)).inputs =
      castObservation
        (parentInputData_eq_stageInputData
          configuration index zero)
        (FFTStageChain.inputObservation configuration step.parent.inputs) := by
  have inputs := wiring.child_inputs (.stage index)
  have markerEqual := congrFun inputs FFTStage.Input.i_first
  have dataEqual := congrFun inputs FFTStage.Input.i_data
  simp only [ModuleBody.Step.wiredChildInputs,
    Wiring.childInputValues, FFTStageChain.wiring, dif_pos zero,
    EndpointContext.moduleInput_value, SignalSource.value_castType]
    at markerEqual dataEqual
  change
    ((step.child (.stage index)).inputs FFTStage.Input.i_first,
      (step.child (.stage index)).inputs FFTStage.Input.i_data) = _
  rw [markerEqual, dataEqual]
  exact pair_cast_eq_castObservation
    (parentInputType_eq_stageInputType configuration index zero)
    (parentInputData_eq_stageInputData configuration index zero)
    _ _

/-- Every later rolled stage observes the preceding stage's output. -/
theorem stageInputObservation_of_wiring_nonzero
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (step : (FFTStageChain.body depth configuration table).Step)
    (wiring : step.WiringHolds)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    FFTStage.inputObservation configuration.arithmetic
        (stageGeometry configuration index)
        (step.child (.stage index)).inputs =
      castObservation
        (previousOutputData_eq_stageInputData
          configuration index nonzero)
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration
            (previousIndex configuration index nonzero))
          (step.child
            (.stage (previousIndex configuration index nonzero))).outputs) := by
  have inputs := wiring.child_inputs (.stage index)
  have markerEqual := congrFun inputs FFTStage.Input.i_first
  have dataEqual := congrFun inputs FFTStage.Input.i_data
  simp only [ModuleBody.Step.wiredChildInputs,
    Wiring.childInputValues, FFTStageChain.wiring, dif_neg nonzero,
    EndpointContext.instanceOutput_value, SignalSource.value_castType]
    at markerEqual dataEqual
  change
    ((step.child (.stage index)).inputs FFTStage.Input.i_first,
      (step.child (.stage index)).inputs FFTStage.Input.i_data) = _
  rw [markerEqual, dataEqual]
  exact pair_cast_eq_castObservation
    (previousOutputType_eq_stageInputType configuration index nonzero)
    (previousOutputData_eq_stageInputData
      configuration index nonzero) _ _

/-- A nonempty chain exposes its final stage output at the parent boundary. -/
theorem parentOutputObservation_of_wiring_nonempty
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (step : (FFTStageChain.body depth configuration table).Step)
    (wiring : step.WiringHolds)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    FFTStageChain.outputObservation configuration step.parent.outputs =
      castObservation
        (lastOutputData_eq_parentOutputData
          configuration nonempty)
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration (lastIndex configuration nonempty))
          (step.child (.stage (lastIndex configuration nonempty))).outputs) := by
  have outputs := wiring.parent_outputs
  have markerEqual := congrFun outputs FFTStageChain.Output.o_first
  have dataEqual := congrFun outputs FFTStageChain.Output.o_data
  simp only [ModuleBody.Step.wiredParentOutputs, FFTStageChain.wiring,
    dif_neg nonempty, EndpointContext.instanceOutput_value,
    SignalSource.value_castType] at markerEqual dataEqual
  change
    (step.parent.outputs FFTStageChain.Output.o_first,
      step.parent.outputs FFTStageChain.Output.o_data) = _
  rw [markerEqual, dataEqual]
  exact pair_cast_eq_castObservation
    (lastOutputType_eq_parentOutputType configuration nonempty)
    (lastOutputData_eq_parentOutputData configuration nonempty)
    _ _

/-- An empty chain exposes its parent input unchanged at the parent output. -/
theorem parentOutputObservation_of_wiring_empty
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (step : (FFTStageChain.body depth configuration table).Step)
    (wiring : step.WiringHolds)
    (empty : depth - configuration.laneDepth = 0) :
    FFTStageChain.outputObservation configuration step.parent.outputs =
      castObservation
        (parentInputData_eq_parentOutputData_of_empty
          configuration empty)
        (FFTStageChain.inputObservation configuration step.parent.inputs) := by
  have outputs := wiring.parent_outputs
  have markerEqual := congrFun outputs FFTStageChain.Output.o_first
  have dataEqual := congrFun outputs FFTStageChain.Output.o_data
  simp only [ModuleBody.Step.wiredParentOutputs, FFTStageChain.wiring,
    dif_pos empty, EndpointContext.moduleInput_value,
    SignalSource.value_castType] at markerEqual dataEqual
  change
    (step.parent.outputs FFTStageChain.Output.o_first,
      step.parent.outputs FFTStageChain.Output.o_data) = _
  rw [markerEqual, dataEqual]
  exact pair_cast_eq_castObservation
    (parentInputType_eq_parentOutputType_of_empty configuration empty)
    (parentInputData_eq_parentOutputData_of_empty
      configuration empty) _ _

/-- Sequence-level form of the first rolled-stage input wiring. -/
theorem stageInputs_eq_parentInputs_zero
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (index : StageIndex configuration) (zero : index.val = 0) :
    (trace.child (.stage index)).inputs.map
        (FFTStage.inputObservation configuration.arithmetic
          (stageGeometry configuration index)) =
      trace.parent.inputs.map (fun input =>
        castObservation
          (parentInputData_eq_stageInputData
            configuration index zero)
          (FFTStageChain.inputObservation configuration input)) := by
  simp only [ModuleBody.Trace.child, ModuleBody.Trace.parent,
    BoundaryTrace.inputs, List.map_map]
  apply List.map_congr_left
  intro step member
  exact stageInputObservation_of_wiring_zero configuration table step
    (wiring.step member) index zero

/-- Sequence-level form of the wiring between consecutive rolled stages. -/
theorem stageInputs_eq_previousOutputs
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    (trace.child (.stage index)).inputs.map
        (FFTStage.inputObservation configuration.arithmetic
          (stageGeometry configuration index)) =
      (trace.child (.stage
        (previousIndex configuration index nonzero))).outputs.map
          (fun output =>
            castObservation
              (previousOutputData_eq_stageInputData
                configuration index nonzero)
              (FFTStage.outputObservation configuration.arithmetic
                (stageGeometry configuration
                  (previousIndex configuration index nonzero)) output)) := by
  simp only [ModuleBody.Trace.child, BoundaryTrace.inputs,
    BoundaryTrace.outputs, List.map_map]
  apply List.map_congr_left
  intro step member
  exact stageInputObservation_of_wiring_nonzero configuration table step
    (wiring.step member) index nonzero

/-- Sequence-level form of a nonempty chain's parent output wiring. -/
theorem parentOutputs_eq_lastOutputs
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    trace.parent.outputs.map (FFTStageChain.outputObservation configuration) =
      (trace.child (.stage
        (lastIndex configuration nonempty))).outputs.map (fun output =>
          castObservation
            (lastOutputData_eq_parentOutputData
              configuration nonempty)
            (FFTStage.outputObservation configuration.arithmetic
              (stageGeometry configuration
                (lastIndex configuration nonempty)) output)) := by
  simp only [ModuleBody.Trace.parent, ModuleBody.Trace.child,
    BoundaryTrace.outputs, List.map_map]
  apply List.map_congr_left
  intro step member
  exact parentOutputObservation_of_wiring_nonempty configuration table step
    (wiring.step member) nonempty

/-- Sequence-level form of an empty chain's identity wiring. -/
theorem parentOutputs_eq_parentInputs_of_empty
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (empty : depth - configuration.laneDepth = 0) :
    trace.parent.outputs.map (FFTStageChain.outputObservation configuration) =
      trace.parent.inputs.map (fun input =>
        castObservation
          (parentInputData_eq_parentOutputData_of_empty
            configuration empty)
          (FFTStageChain.inputObservation configuration input)) := by
  simp only [ModuleBody.Trace.parent, BoundaryTrace.inputs,
    BoundaryTrace.outputs, List.map_map]
  apply List.map_congr_left
  intro step member
  exact parentOutputObservation_of_wiring_empty configuration table step
    (wiring.step member) empty

end HTFFT.Silean.FFT.FFTStageChain.Internal
