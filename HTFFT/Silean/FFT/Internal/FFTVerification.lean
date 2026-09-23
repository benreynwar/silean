import HTFFT.Silean.FFT.Internal.FFTComposition
import HTFFT.Silean.FFT.Internal.FFTStructure
import Silean.Semantics.ModuleBodyTrace

/-! Conditional correctness of the permanent top-level FFT body. -/

namespace HTFFT.Silean.FFT.Internal

open _root_.Silean
open _root_.Silean.Modules

private def withMarkers {length : Nat} {α β : Type}
    (function : FramedLatency.Frame length α →
      FramedLatency.Frame length β) :
    FramedLatency.Frame length (Bool × α) →
      FramedLatency.Frame length (Bool × β) :=
  fun frame cycle => ((frame cycle).1,
    function (fun index => (frame index).2) cycle)

private theorem initialInputs_eq_parentInputs
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .initialReorder).inputs.map
        (InitialReorder.inputObservation configuration) =
      trace.parent.inputs.map (FFT.inputObservation configuration) := by
  rw [wiring.child_inputs .initialReorder]
  simp [ModuleBody.Step.wiredChildInputs,
    InitialReorder.inputObservation, FFT.inputObservation,
    FFT.wiring, FFT.context, ModuleBody.Trace.parent,
    BoundaryTrace.inputs]

private theorem unrolledInputs_eq_initialData
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .unrolled).inputs.map (fun input => input .input) =
      (trace.child .initialReorder).outputs.map
        (fun output =>
          (InitialReorder.outputObservation configuration output).2) := by
  rw [wiring.child_inputs .unrolled]
  simp only [List.map_map, ModuleBody.Trace.child, BoundaryTrace.outputs]
  apply List.map_congr_left
  intro step _
  rfl

private theorem markerDelayInputs_eq_initialMarkers
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .unrolledFirstDelay).inputs.map
        (fun input => input .input) =
      (trace.child .initialReorder).outputs.map
        (fun output =>
          (InitialReorder.outputObservation configuration output).1) := by
  rw [wiring.child_inputs .unrolledFirstDelay]
  simp only [List.map_map, ModuleBody.Trace.child, BoundaryTrace.outputs]
  apply List.map_congr_left
  intro step _
  rfl

private theorem markerDelayOutputs_eq_stageMarkers
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .unrolledFirstDelay).outputs.map
        (fun output => output .output) =
      (trace.child .stageChain).inputs.map
        (fun input =>
          (FFTStageChain.inputObservation configuration input).1) := by
  rw [wiring.child_inputs .stageChain]
  simp only [List.map_map, ModuleBody.Trace.child, BoundaryTrace.outputs]
  apply List.map_congr_left
  intro step _
  rfl

private theorem unrolledOutputs_eq_stageData
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .unrolled).outputs.map (fun output => output .output) =
      (trace.child .stageChain).inputs.map
        (fun input =>
          (FFTStageChain.inputObservation configuration input).2) := by
  rw [wiring.child_inputs .stageChain]
  simp only [List.map_map, ModuleBody.Trace.child, BoundaryTrace.outputs]
  apply List.map_congr_left
  intro step _
  rfl

private theorem finalInputs_eq_stageOutputs
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    (trace.child .finalReorder).inputs.map
        (FinalReorder.inputObservation configuration) =
      (trace.child .stageChain).outputs.map
        (FFTStageChain.outputObservation configuration) := by
  rw [wiring.child_inputs .finalReorder]
  simp [ModuleBody.Step.wiredChildInputs, FinalReorder.inputObservation,
    FFTStageChain.outputObservation, FFT.wiring, FFT.context,
    ModuleBody.Trace.child, BoundaryTrace.outputs]

private theorem parentOutputs_eq_finalOutputs
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds) :
    trace.parent.outputs.map (FFT.outputObservation configuration) =
      (trace.child .finalReorder).outputs.map
        (FinalReorder.outputObservation configuration) := by
  rw [wiring.parent_outputs]
  simp [ModuleBody.Step.wiredParentOutputs, FFT.outputObservation,
    FinalReorder.outputObservation, FFT.wiring, FFT.context,
    ModuleBody.Trace.child, BoundaryTrace.outputs]

/-- The permanent body satisfies the complete FFT contract whenever each
unresolved functional child, the existing unrolled network, and the separate
marker shift register satisfy their own public trace contracts. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (trace : (FFT.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (initialCorrect : InitialReorder.contract configuration
      (trace.child .initialReorder))
    (unrolledCorrect : UnrolledFFTNetwork.contract configuration.unrolled
      (configuration.prefixTable table) (trace.child .unrolled))
    (markerDelayCorrect : OptionalShiftRegister.contract .bit
      configuration.unrolled.networkLatency
      (trace.child .unrolledFirstDelay))
    (stageChainCorrect : FFTStageChain.contract configuration table
      (trace.child .stageChain))
    (finalCorrect : FinalReorder.contract configuration
      (trace.child .finalReorder)) :
    FFT.contract configuration table trace.parent := by
  have initialRelation :=
    InitialReorder.relates_of_contract configuration initialCorrect
  unfold InitialReorder.carriedRelation at initialRelation
  have initialComputation :
      FramedLatency.Computes configuration.frameLength
        configuration.initialReorderLatency configuration.frameLength_pos
        (fun input : InitialReorder.InputObservation configuration =>
          input.1 = true)
        (fun output : InitialReorder.OutputObservation configuration =>
          output.1 = true)
        (withMarkers (InitialReorder.resultFrame configuration))
        (trace.parent.inputs.map (FFT.inputObservation configuration))
        ((trace.child .initialReorder).outputs.map
          (InitialReorder.outputObservation configuration)) := by
    have deterministic :=
      FramedLatency.computes_of_payload_relation initialRelation
    rw [initialInputs_eq_parentInputs configuration table trace wiring]
      at deterministic
    exact deterministic

  unfold UnrolledFFTNetwork.contract at unrolledCorrect
  have payloadComputation :
      FixedLatency.Computes configuration.unrolled.networkLatency
        (fun input : InputData configuration =>
          UnrolledFFTLayer.encodeVector
            (configuration.unrolled.boundaryFormat
              (Fin.last configuration.laneDepth))
            (UnrolledFFTNetwork.resultValue configuration.unrolled
              (configuration.prefixTable table) input))
        ((trace.child .unrolled).inputs.map
          (fun input => input UnrolledFFTNetwork.Input.input))
        ((trace.child .unrolled).outputs.map
          (fun output => output UnrolledFFTNetwork.Output.output)) :=
    FixedLatency.computes_of_holds_projection
      (fun input :
        (UnrolledFFTNetwork.ports configuration.unrolled).inputs.Values =>
        input UnrolledFFTNetwork.Input.input)
      (fun output :
        (UnrolledFFTNetwork.ports configuration.unrolled).outputs.Values =>
        output UnrolledFFTNetwork.Output.output) unrolledCorrect
  have payloadComputation := FixedLatency.computes_congr_inputs
    (unrolledInputs_eq_initialData configuration table trace wiring)
    payloadComputation
  have payloadComputation := FixedLatency.computes_congr_outputs
    (unrolledOutputs_eq_stageData configuration table trace wiring)
    payloadComputation
  change FixedLatency.Computes configuration.unrolled.networkLatency
    (fun input : InputData configuration =>
      (UnrolledFFTLayer.encodeVector
        (configuration.unrolled.boundaryFormat
          (Fin.last configuration.laneDepth))
        (UnrolledFFTNetwork.resultValue configuration.unrolled
          (configuration.prefixTable table) input) : PrefixData configuration))
    ((trace.child .initialReorder).outputs.map
      (fun output =>
        (InitialReorder.outputObservation configuration output).2))
    ((trace.child .stageChain).inputs.map
      (fun input => (FFTStageChain.inputObservation configuration input).2))
    at payloadComputation
  unfold OptionalShiftRegister.contract at markerDelayCorrect
  have markerComputation :
      FixedLatency.Computes configuration.unrolled.networkLatency id
        ((trace.child .unrolledFirstDelay).inputs.map
          (fun input => input ShiftRegister.Input.input))
        ((trace.child .unrolledFirstDelay).outputs.map
          (fun output => output ShiftRegister.Output.output)) :=
    FixedLatency.computes_of_holds_projection
      (fun input : (ShiftRegister.ports .bit).inputs.Values =>
        input ShiftRegister.Input.input)
      (fun output : (ShiftRegister.ports .bit).outputs.Values =>
        output ShiftRegister.Output.output) markerDelayCorrect
  have markerComputation := FixedLatency.computes_congr_inputs
    (markerDelayInputs_eq_initialMarkers configuration table trace wiring)
    markerComputation
  have markerComputation := FixedLatency.computes_congr_outputs
    (markerDelayOutputs_eq_stageMarkers configuration table trace wiring)
    markerComputation
  change FixedLatency.Computes configuration.unrolled.networkLatency
    (id : Bool → Bool)
    ((trace.child .initialReorder).outputs.map
      (fun output =>
        (InitialReorder.outputObservation configuration output).1))
    ((trace.child .stageChain).inputs.map
      (fun input => (FFTStageChain.inputObservation configuration input).1))
    at markerComputation
  have unrolledComputation :
      FramedLatency.Computes configuration.frameLength
        configuration.unrolled.networkLatency configuration.frameLength_pos
        (fun input : InitialReorder.OutputObservation configuration =>
          input.1 = true)
        (fun output : FFTStageChain.InputObservation configuration =>
          output.1 = true)
        (withMarkers (unrolledResultFrame configuration table))
        ((trace.child .initialReorder).outputs.map
          (InitialReorder.outputObservation configuration))
        ((trace.child .stageChain).inputs.map
          (FFTStageChain.inputObservation configuration)) := by
    have markerForPairs :
        FixedLatency.Computes configuration.unrolled.networkLatency id
          (((trace.child .initialReorder).outputs.map
            (InitialReorder.outputObservation configuration)).map
              (fun value => value.1))
          (((trace.child .stageChain).inputs.map
            (FFTStageChain.inputObservation configuration)).map
              (fun value => value.1)) := by
      simpa [SignalType.Denote, List.map_map, Function.comp_def] using
        markerComputation
    have payloadForPairs :
        FixedLatency.Computes configuration.unrolled.networkLatency
          (fun input : InputData configuration =>
            UnrolledFFTLayer.encodeVector
              (configuration.unrolled.boundaryFormat
                (Fin.last configuration.laneDepth))
              (UnrolledFFTNetwork.resultValue configuration.unrolled
                (configuration.prefixTable table) input))
          (((trace.child .initialReorder).outputs.map
            (InitialReorder.outputObservation configuration)).map
              (fun value => (value.2 : InputData configuration)))
          (((trace.child .stageChain).inputs.map
            (FFTStageChain.inputObservation configuration)).map
              (fun value => (value.2 : PrefixData configuration))) := by
      simpa only [List.map_map, Function.comp_def,
        Configuration.prefixGeometry_laneCount,
        Configuration.prefixGeometry_laneDepth,
        Configuration.prefixGeometry_completed] using
        payloadComputation
    have synchronized := FramedLatency.computes_of_components
        (frameLength := configuration.frameLength)
        (latency := configuration.unrolled.networkLatency)
        (positive := configuration.frameLength_pos)
        (function := fun input : InputData configuration =>
          (UnrolledFFTLayer.encodeVector
            (configuration.unrolled.boundaryFormat
              (Fin.last configuration.laneDepth))
            (UnrolledFFTNetwork.resultValue configuration.unrolled
              (configuration.prefixTable table) input) :
            PrefixData configuration))
        (inputs := (trace.child .initialReorder).outputs.map
          (InitialReorder.outputObservation configuration))
        (outputs := (trace.child .stageChain).inputs.map
          (FFTStageChain.inputObservation configuration))
        markerForPairs payloadForPairs
    change FramedLatency.Computes configuration.frameLength
      configuration.unrolled.networkLatency configuration.frameLength_pos
      (fun input : InitialReorder.OutputObservation configuration =>
        input.1 = true)
      (fun output : FFTStageChain.InputObservation configuration =>
        output.1 = true)
      (withMarkers (unrolledResultFrame configuration table))
      ((trace.child .initialReorder).outputs.map
        (InitialReorder.outputObservation configuration))
      ((trace.child .stageChain).inputs.map
        (FFTStageChain.inputObservation configuration)) at synchronized
    exact synchronized

  have stageRelation :=
    FFTStageChain.relates_of_contract configuration table stageChainCorrect
  unfold FFTStageChain.carriedRelation at stageRelation
  have stageComputation :
      FramedLatency.Computes configuration.frameLength
        configuration.stageChainLatency configuration.frameLength_pos
        (fun input : FFTStageChain.InputObservation configuration =>
          input.1 = true)
        (fun output : FFTStageChain.OutputObservation configuration =>
          output.1 = true)
        (withMarkers (FFTStageChain.resultFrame configuration table))
        ((trace.child .stageChain).inputs.map
          (FFTStageChain.inputObservation configuration))
        ((trace.child .stageChain).outputs.map
          (FFTStageChain.outputObservation configuration)) := by
    exact FramedLatency.computes_of_payload_relation stageRelation

  have finalRelation :=
    FinalReorder.relates_of_contract configuration finalCorrect
  unfold FinalReorder.carriedRelation at finalRelation
  have finalComputation :
      FramedLatency.Computes configuration.frameLength
        configuration.finalReorderLatency configuration.frameLength_pos
        (fun input : FFTStageChain.OutputObservation configuration =>
          input.1 = true)
        (fun output : FFT.OutputObservation configuration =>
          output.1 = true)
        (withMarkers (FinalReorder.resultFrame configuration))
        ((trace.child .stageChain).outputs.map
          (FFTStageChain.outputObservation configuration))
        (trace.parent.outputs.map (FFT.outputObservation configuration)) := by
    have deterministic :=
      FramedLatency.computes_of_payload_relation finalRelation
    rw [finalInputs_eq_stageOutputs configuration table trace wiring]
      at deterministic
    rw [← parentOutputs_eq_finalOutputs configuration table trace wiring]
      at deterministic
    exact deterministic

  have throughUnrolled := FramedLatency.computes_serial
    initialComputation unrolledComputation
  have throughStages := FramedLatency.computes_serial
    throughUnrolled stageComputation
  have composed := FramedLatency.computes_serial throughStages finalComputation
  have topRelation :
      FramedLatency.Relates configuration.frameLength
        configuration.totalLatency configuration.frameLength_pos
        (fun input : FFT.InputObservation configuration => input.1 = true)
        (fun output : FFT.OutputObservation configuration => output.1 = true)
        (FFT.carriedRelation configuration table)
        (trace.parent.inputs.map (FFT.inputObservation configuration))
        (trace.parent.outputs.map (FFT.outputObservation configuration)) := by
    simpa only [Configuration.totalLatency] using
      FramedLatency.mono composed (fun input output equal => by
        unfold FFT.carriedRelation
        rw [equal]
        funext cycle
        exact congrFun (resultFrame_composition configuration table
          (fun index => (input index).2)) cycle)
  unfold FFT.contract
  change FramedLatency.Holds configuration.frameLength
    configuration.totalLatency configuration.frameLength_pos
    (fun input => (FFT.inputObservation configuration input).1 = true)
    (fun output => (FFT.outputObservation configuration output).1 = true)
    (fun input output => FFT.carriedRelation configuration table
      (fun cycle => FFT.inputObservation configuration (input cycle))
      (fun cycle => FFT.outputObservation configuration (output cycle)))
    trace.parent
  exact FramedLatency.holds_of_relates_projection
      (inputFirst := fun input : FFT.InputObservation configuration =>
        input.1 = true)
      (outputFirst := fun output : FFT.OutputObservation configuration =>
        output.1 = true)
      (relation := FFT.carriedRelation configuration table)
      (FFT.inputObservation configuration) (FFT.outputObservation configuration)
      topRelation

end HTFFT.Silean.FFT.Internal
