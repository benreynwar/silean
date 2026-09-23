import HTFFT.Silean.FFT.Internal.FFTStageChainWiring
import HTFFT.Silean.FFTStage.FFTStageComposition

/-! Conditional correctness of the permanent rolled-stage chain body. -/

namespace HTFFT.Silean.FFT.FFTStageChain.Internal

open _root_.Silean

/-- Deterministic observation-level function specified by one stage's public
contract. -/
private def stageFunction (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration) :
    FramedLatency.Frame configuration.frameLength
        (FFTStage.InputObservation configuration.arithmetic
          (stageGeometry configuration index)) →
      FramedLatency.Frame configuration.frameLength
        (FFTStage.OutputObservation configuration.arithmetic
          (stageGeometry configuration index)) :=
  fun frame cycle =>
    ((frame cycle).1,
      FFTStage.encodeOutputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (FFTStage.resultValue configuration.arithmetic table
          (stageGeometry configuration index)
          (fun inputCycle => (frame inputCycle).2)) cycle)

/-- The public contract of one unresolved child gives its deterministic
observation-level framed computation. -/
private theorem stageComputation
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic table
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index)))
    (index : StageIndex configuration) :
    FramedLatency.Computes configuration.frameLength (stageLatency index)
      configuration.frameLength_pos
      (fun input : FFTStage.InputObservation configuration.arithmetic
        (stageGeometry configuration index) => input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      (stageFunction configuration table index)
      ((trace.child (.stage index)).inputs.map
        (FFTStage.inputObservation configuration.arithmetic
          (stageGeometry configuration index)))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) := by
  have related := FFTStage.relates_of_contract configuration.arithmetic table
    (stageGeometry configuration index) (stageLatency index)
    (stageCorrect index)
  unfold FFTStage.carriedRelation at related
  have deterministic := FramedLatency.computes_of_payload_relation
    (frameLength := configuration.frameLength)
    (latency := stageLatency index)
    (positive := configuration.frameLength_pos)
    (function := fun input =>
      FFTStage.encodeOutputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (FFTStage.resultValue configuration.arithmetic table
          (stageGeometry configuration index) input))
    related
  exact deterministic

/-- Latency accumulated through and including a selected rolled stage. -/
private def latencyThrough (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat)
    (index : StageIndex configuration) : Nat :=
  (((List.finRange (stageCount depth configuration)).take (index.val + 1)).map
    stageLatency).sum

/-- Rolled stages applied through and including a selected family member. -/
private def stagesThrough (configuration : Configuration depth)
    (index : StageIndex configuration) : List (Fin depth) :=
  ((List.finRange (stageCount depth configuration)).take (index.val + 1)).map
    (fun stage => (stageGeometry configuration stage).stage)

private theorem latencyThrough_zero
    (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat)
    (index : StageIndex configuration) (zero : index.val = 0) :
    latencyThrough configuration stageLatency index = stageLatency index := by
  have countPositive : 0 < stageCount depth configuration := by
    have := index.isLt
    omega
  have indexEqual : index = ⟨0, by omega⟩ := by
    apply Fin.ext
    exact zero
  rw [indexEqual]
  unfold latencyThrough
  rw [List.take_succ_eq_append_getElem (i := 0) (by simpa using countPositive),
    List.map_append]
  simp

private theorem latencyThrough_nonzero
    (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    latencyThrough configuration stageLatency index =
      latencyThrough configuration stageLatency
          (previousIndex configuration index nonzero) +
        stageLatency index := by
  unfold latencyThrough
  rw [List.take_succ_eq_append_getElem (by simp),
    List.map_append,
    List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  congr 1
  · congr 2
    simp [previousIndex]
    omega
  · congr 1
    simp

private theorem stagesThrough_zero
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    stagesThrough configuration index =
      [(stageGeometry configuration index).stage] := by
  have countPositive : 0 < stageCount depth configuration := by
    have := index.isLt
    omega
  have indexEqual : index = ⟨0, by omega⟩ := by
    apply Fin.ext
    exact zero
  rw [indexEqual]
  unfold stagesThrough
  rw [List.take_succ_eq_append_getElem (i := 0) (by simp [countPositive]),
    List.map_append]
  simp

private theorem stagesThrough_nonzero
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    stagesThrough configuration index =
      stagesThrough configuration
          (previousIndex configuration index nonzero) ++
        [(stageGeometry configuration index).stage] := by
  unfold stagesThrough
  rw [List.take_succ_eq_append_getElem (by simp),
    List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 1
  · congr 2
    simp [previousIndex]
    omega
  · congr 2
    simp

private theorem stagesThrough_eq_previous_and_current
    (configuration : Configuration depth)
    (index : StageIndex configuration) :
    stagesThrough configuration index =
      ((List.finRange (stageCount depth configuration)).take index.val).map
          (fun stage => (stageGeometry configuration stage).stage) ++
        [(stageGeometry configuration index).stage] := by
  unfold stagesThrough
  rw [List.take_succ_eq_append_getElem (by simp),
    List.map_append]
  simp

/-- Pure logical value after a selected prefix of rolled stages. -/
private def resultValueThrough (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration)
    (input : PrefixFrame configuration) : HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.applyButterflyLayers configuration.arithmetic.fixedConfig
    table (stagesThrough configuration index)
    (decodePrefix configuration input)

/-- Every nonempty rolled prefix ends in the selected butterfly stage, so its
result is canonical at that stage's output format. -/
private theorem resultValueThrough_canonical
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration)
    (input : PrefixFrame configuration) :
    (fun valueIndex => HTFFT.Butterfly.Fixed.wrapComplex
      (configuration.arithmetic.boundaryFormat
        (stageGeometry configuration index).stage.succ)
      (resultValueThrough configuration table index input valueIndex)) =
      resultValueThrough configuration table index input := by
  rw [resultValueThrough,
    stagesThrough_eq_previous_and_current configuration index,
    HTFFT.Fixed.applyButterflyLayers_append]
  exact HTFFT.Fixed.wrapComplex_butterflyLayer
    configuration.arithmetic.fixedConfig table
    (stageGeometry configuration index).stage _

/-- Pure packed frame produced after a selected prefix of rolled stages. -/
private def resultFrameThrough (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration)
    (input : PrefixFrame configuration) :
    FFTStage.OutputFrame configuration.arithmetic
      (stageGeometry configuration index) :=
  FFTStage.encodeOutputFrame configuration.arithmetic
    (stageGeometry configuration index)
    (resultValueThrough configuration table index input)

/-- Observation-level form of `resultFrameThrough`. -/
private def functionThrough (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration) :
    FramedLatency.Frame configuration.frameLength
        (FFTStageChain.InputObservation configuration) →
      FramedLatency.Frame configuration.frameLength
        (FFTStage.OutputObservation configuration.arithmetic
          (stageGeometry configuration index)) :=
  fun frame cycle =>
    ((frame cycle).1,
      resultFrameThrough configuration table index
        (fun inputCycle => (frame inputCycle).2) cycle)

/-- Deterministic observation-level function in the public chain contract. -/
private def chainFunction (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    FramedLatency.Frame configuration.frameLength
        (FFTStageChain.InputObservation configuration) →
      FramedLatency.Frame configuration.frameLength
        (FFTStageChain.OutputObservation configuration) :=
  fun frame cycle =>
    ((frame cycle).1,
      FFTStageChain.resultFrame configuration table
        (fun inputCycle => (frame inputCycle).2) cycle)

private theorem decode_firstStage_cast
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0)
    (input : PrefixFrame configuration) :
    FFTStage.decodeInputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (fun cycle =>
          Eq.mp (parentInputData_eq_stageInputData configuration index zero)
            (input cycle)) =
      decodePrefix configuration input := by
  let boundaryEqual :=
    (firstStage_inputBoundary configuration index zero).symm
  have framesEqual :
      (fun cycle =>
        Eq.mp (parentInputData_eq_stageInputData configuration index zero)
          (input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input := by
    funext cycle
    rw [FFTStage.castBoundaryFrame_apply]
    have cycleEqual :
        Fin.cast
            (congrArg FFTStage.BoundaryGeometry.frameLength
              boundaryEqual).symm cycle = cycle := by
      apply Fin.ext
      rfl
    rw [cycleEqual]
    have dataProof :
        parentInputData_eq_stageInputData configuration index zero =
          congrArg (FFTStage.BoundaryData configuration.arithmetic)
            boundaryEqual := Subsingleton.elim _ _
    rw [dataProof]
    exact (FFTStage.castBoundaryData_eq_mp
      configuration.arithmetic boundaryEqual (input cycle)).symm
  calc
    FFTStage.decodeInputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (fun cycle =>
          Eq.mp
            (parentInputData_eq_stageInputData configuration index zero)
            (input cycle)) =
      FFTStage.decodeBoundaryFrame configuration.arithmetic
        (stageGeometry configuration index).inputBoundary
        (FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input) := congrArg
            (FFTStage.decodeBoundaryFrame configuration.arithmetic
              (stageGeometry configuration index).inputBoundary) framesEqual
    _ = FFTStage.decodeBoundaryFrame configuration.arithmetic
        configuration.prefixGeometry input :=
      FFTStage.decodeBoundaryFrame_cast configuration.arithmetic
        boundaryEqual input
    _ = decodePrefix configuration input := rfl

private theorem functionThrough_zero
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    stageFunction configuration table index ∘
        (fun frame cycle =>
          castObservation
            (parentInputData_eq_stageInputData configuration index zero)
            (frame cycle)) =
      functionThrough configuration table index := by
  funext frame cycle
  apply Prod.ext
  · rfl
  · let inputData : PrefixFrame configuration :=
      fun inputCycle => (frame inputCycle).2
    change
      FFTStage.encodeOutputFrame configuration.arithmetic
          (stageGeometry configuration index)
          (FFTStage.resultValue configuration.arithmetic table
            (stageGeometry configuration index)
            (fun inputCycle =>
              Eq.mp
                (parentInputData_eq_stageInputData configuration index zero)
                (inputData inputCycle))) cycle =
        resultFrameThrough configuration table index
          inputData cycle
    unfold FFTStage.resultValue resultFrameThrough resultValueThrough
    rw [decode_firstStage_cast configuration index zero,
      stagesThrough_zero configuration index zero]
    rfl

private theorem decode_previousStage_cast
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0)
    (input : FFTStage.OutputFrame configuration.arithmetic
      (stageGeometry configuration
        (previousIndex configuration index nonzero))) :
    FFTStage.decodeInputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (fun cycle =>
          Eq.mp
            (previousOutputData_eq_stageInputData configuration index nonzero)
            (input cycle)) =
      FFTStage.decodeOutputFrame configuration.arithmetic
        (stageGeometry configuration
          (previousIndex configuration index nonzero)) input := by
  let boundaryEqual :=
    previousStage_outputBoundary configuration index nonzero
  have framesEqual :
      (fun cycle =>
        Eq.mp
          (previousOutputData_eq_stageInputData configuration index nonzero)
          (input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input := by
    funext cycle
    rw [FFTStage.castBoundaryFrame_apply]
    have cycleEqual :
        Fin.cast
            (congrArg FFTStage.BoundaryGeometry.frameLength
              boundaryEqual).symm cycle = cycle := by
      apply Fin.ext
      rfl
    rw [cycleEqual]
    have dataProof :
        previousOutputData_eq_stageInputData configuration index nonzero =
          congrArg (FFTStage.BoundaryData configuration.arithmetic)
            boundaryEqual := Subsingleton.elim _ _
    rw [dataProof]
    exact (FFTStage.castBoundaryData_eq_mp
      configuration.arithmetic boundaryEqual (input cycle)).symm
  calc
    FFTStage.decodeInputFrame configuration.arithmetic
        (stageGeometry configuration index)
        (fun cycle =>
          Eq.mp
            (previousOutputData_eq_stageInputData configuration index nonzero)
            (input cycle)) =
      FFTStage.decodeBoundaryFrame configuration.arithmetic
        (stageGeometry configuration index).inputBoundary
        (FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input) := congrArg
            (FFTStage.decodeBoundaryFrame configuration.arithmetic
              (stageGeometry configuration index).inputBoundary) framesEqual
    _ = FFTStage.decodeBoundaryFrame configuration.arithmetic
        (stageGeometry configuration
          (previousIndex configuration index nonzero)).outputBoundary input :=
      FFTStage.decodeBoundaryFrame_cast configuration.arithmetic
        boundaryEqual input
    _ = FFTStage.decodeOutputFrame configuration.arithmetic
        (stageGeometry configuration
          (previousIndex configuration index nonzero)) input := rfl

private theorem functionThrough_nonzero
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    stageFunction configuration table index ∘
        (fun frame cycle =>
          castObservation
            (previousOutputData_eq_stageInputData configuration index nonzero)
            (functionThrough configuration table
              (previousIndex configuration index nonzero) frame cycle)) =
      functionThrough configuration table index := by
  funext frame cycle
  apply Prod.ext
  · rfl
  · let inputData : PrefixFrame configuration :=
      fun inputCycle => (frame inputCycle).2
    let previous := previousIndex configuration index nonzero
    let previousFrame :
        FFTStage.OutputFrame configuration.arithmetic
          (stageGeometry configuration previous) :=
      resultFrameThrough configuration table previous inputData
    change
      FFTStage.encodeOutputFrame configuration.arithmetic
          (stageGeometry configuration index)
          (FFTStage.resultValue configuration.arithmetic table
            (stageGeometry configuration index)
            (fun inputCycle =>
              Eq.mp
                (previousOutputData_eq_stageInputData configuration index
                  nonzero)
                (previousFrame inputCycle))) cycle =
        resultFrameThrough configuration table index inputData cycle
    unfold FFTStage.resultValue resultFrameThrough
    rw [decode_previousStage_cast configuration index nonzero previousFrame]
    change
      FFTStage.encodeOutputFrame configuration.arithmetic
          (stageGeometry configuration index)
          (HTFFT.Fixed.butterflyLayer
            configuration.arithmetic.fixedConfig table
            (stageGeometry configuration index).stage
            (FFTStage.decodeOutputFrame configuration.arithmetic
              (stageGeometry configuration previous)
              (FFTStage.encodeOutputFrame configuration.arithmetic
                (stageGeometry configuration previous)
                (resultValueThrough configuration table previous
                  inputData)))) cycle = _
    rw [FFTStage.decodeOutputFrame_encodeOutputFrame,
      resultValueThrough_canonical configuration table previous inputData]
    unfold resultValueThrough
    rw [stagesThrough_nonzero configuration index nonzero,
      HTFFT.Fixed.applyButterflyLayers_append]
    rfl

/-- Induction invariant for the rolled family: the parent input reaches the
selected child output after exactly the prefix sum of child latencies and has
undergone exactly the corresponding prefix of fixed-point layers. -/
private theorem computationThrough
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic table
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index)))
    (index : StageIndex configuration) :
    FramedLatency.Computes configuration.frameLength
      (latencyThrough configuration stageLatency index)
      configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      (functionThrough configuration table index)
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) := by
  by_cases zero : index.val = 0
  · have current := stageComputation configuration table stageLatency trace
      stageCorrect index
    rw [stageInputs_eq_parentInputs_zero configuration table trace wiring
      index zero] at current
    have currentMappedInputs : FramedLatency.Computes configuration.frameLength
      (stageLatency index) configuration.frameLength_pos
      (fun input : FFTStage.InputObservation configuration.arithmetic
        (stageGeometry configuration index) => input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      (stageFunction configuration table index)
      ((trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration)).map
          (castObservation
            (parentInputData_eq_stageInputData configuration index zero)))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) := by
      simpa only [List.map_map, Function.comp_def] using current
    have mapped := FramedLatency.computes_map_inputs
      (castObservation
        (parentInputData_eq_stageInputData configuration index zero))
      currentMappedInputs
    rw [latencyThrough_zero configuration stageLatency index zero]
    have mappedNormalized : FramedLatency.Computes configuration.frameLength
      (stageLatency index) configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      (stageFunction configuration table index ∘
        (fun frame cycle =>
          castObservation
            (parentInputData_eq_stageInputData configuration index zero)
            (frame cycle)))
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) := by
      simpa only [castObservation_fst, Function.comp_def] using mapped
    rw [functionThrough_zero configuration table index zero] at mappedNormalized
    exact mappedNormalized
  · let previous := previousIndex configuration index zero
    have previousComputation := computationThrough configuration table
      stageLatency trace wiring stageCorrect previous
    have current := stageComputation configuration table stageLatency trace
      stageCorrect index
    rw [stageInputs_eq_previousOutputs configuration table trace wiring
      index zero] at current
    have currentMappedInputs : FramedLatency.Computes configuration.frameLength
      (stageLatency index) configuration.frameLength_pos
      (fun input : FFTStage.InputObservation configuration.arithmetic
        (stageGeometry configuration index) => input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      (stageFunction configuration table index)
      (((trace.child (.stage previous)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration previous))).map
            (castObservation
              (previousOutputData_eq_stageInputData configuration index zero)))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) := by
      simpa only [List.map_map, Function.comp_def] using current
    have currentFromPrevious := FramedLatency.computes_map_inputs
      (castObservation
        (previousOutputData_eq_stageInputData configuration index zero))
      currentMappedInputs
    have composed := FramedLatency.computes_serial previousComputation
      currentFromPrevious
    rw [latencyThrough_nonzero configuration stageLatency index zero]
    change FramedLatency.Computes configuration.frameLength
      (latencyThrough configuration stageLatency previous +
        stageLatency index) configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration index) => output.1 = true)
      ((stageFunction configuration table index ∘
          (fun frame cycle =>
            castObservation
              (previousOutputData_eq_stageInputData configuration index zero)
              (frame cycle))) ∘
        functionThrough configuration table previous)
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      ((trace.child (.stage index)).outputs.map
        (FFTStage.outputObservation configuration.arithmetic
          (stageGeometry configuration index))) at composed
    have functionEqual := functionThrough_nonzero configuration table index zero
    change
      (stageFunction configuration table index ∘
          (fun frame cycle =>
            castObservation
              (previousOutputData_eq_stageInputData configuration index zero)
              (frame cycle))) ∘
        functionThrough configuration table previous =
      functionThrough configuration table index at functionEqual
    rw [functionEqual] at composed
    exact composed
termination_by index.val
decreasing_by
  simp [previousIndex]
  omega

private theorem latencyThrough_last
    (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat)
    (nonempty : stageCount depth configuration ≠ 0) :
    latencyThrough configuration stageLatency
        (lastIndex configuration nonempty) =
      FFTStageChain.accumulatedLatency configuration stageLatency := by
  change depth - configuration.laneDepth ≠ 0 at nonempty
  unfold latencyThrough FFTStageChain.accumulatedLatency
  have throughAll :
      (lastIndex configuration nonempty).val + 1 =
        stageCount depth configuration := by
    change depth - configuration.laneDepth - 1 + 1 =
      depth - configuration.laneDepth
    omega
  rw [throughAll]
  have takeAll :
      (List.finRange (stageCount depth configuration)).take
          (stageCount depth configuration) =
        List.finRange (stageCount depth configuration) := by
    simp
  rw [takeAll]

private theorem allRolledStages_eq_suffix
    (configuration : Configuration depth) :
    (List.finRange (stageCount depth configuration)).map
        (fun index => (stageGeometry configuration index).stage) =
      HTFFT.Exact.butterflyStageSuffix depth
        configuration.prefixBoundary := by
  apply List.ext_getElem
  · simp [HTFFT.Exact.butterflyStageSuffix,
      HTFFT.Exact.butterflyStages, stageCount]
  · intro position leftWithin rightWithin
    apply Fin.ext
    simp [HTFFT.Exact.butterflyStageSuffix,
      HTFFT.Exact.butterflyStages, stageGeometry]

private theorem stagesThrough_last
    (configuration : Configuration depth)
    (nonempty : stageCount depth configuration ≠ 0) :
    stagesThrough configuration (lastIndex configuration nonempty) =
      HTFFT.Exact.butterflyStageSuffix depth
        configuration.prefixBoundary := by
  change depth - configuration.laneDepth ≠ 0 at nonempty
  unfold stagesThrough
  have throughAll :
      (lastIndex configuration nonempty).val + 1 =
        stageCount depth configuration := by
    change depth - configuration.laneDepth - 1 + 1 =
      depth - configuration.laneDepth
    omega
  rw [throughAll]
  have takeAll :
      (List.finRange (stageCount depth configuration)).take
          (stageCount depth configuration) =
        List.finRange (stageCount depth configuration) := by
    simp
  rw [takeAll]
  exact allRolledStages_eq_suffix configuration

private theorem resultFrameThrough_last_cast
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (nonempty : stageCount depth configuration ≠ 0)
    (input : PrefixFrame configuration) :
    (fun cycle =>
      Eq.mp (lastOutputData_eq_parentOutputData configuration nonempty)
        (resultFrameThrough configuration table
          (lastIndex configuration nonempty) input cycle)) =
      FFTStageChain.resultFrame configuration table input := by
  let last := lastIndex configuration nonempty
  let boundaryEqual := lastStage_outputBoundary configuration nonempty
  have framesEqual :
      (fun cycle =>
        Eq.mp (lastOutputData_eq_parentOutputData configuration nonempty)
          (resultFrameThrough configuration table last input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          (resultFrameThrough configuration table last input) := by
    funext cycle
    rw [FFTStage.castBoundaryFrame_apply]
    have cycleEqual :
        Fin.cast
            (congrArg FFTStage.BoundaryGeometry.frameLength
              boundaryEqual).symm cycle = cycle := by
      apply Fin.ext
      rfl
    rw [cycleEqual]
    have dataProof :
        lastOutputData_eq_parentOutputData configuration nonempty =
          congrArg (FFTStage.BoundaryData configuration.arithmetic)
            boundaryEqual := Subsingleton.elim _ _
    rw [dataProof]
    exact (FFTStage.castBoundaryData_eq_mp configuration.arithmetic
      boundaryEqual (resultFrameThrough configuration table last input cycle)).symm
  calc
    (fun cycle =>
      Eq.mp (lastOutputData_eq_parentOutputData configuration nonempty)
        (resultFrameThrough configuration table last input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          (resultFrameThrough configuration table last input) := framesEqual
    _ = FFTStage.encodeBoundaryFrame configuration.arithmetic
        configuration.finalGeometry
        (resultValueThrough configuration table last input) := by
      unfold resultFrameThrough FFTStage.encodeOutputFrame
      exact FFTStage.castBoundaryFrame_encodeBoundaryFrame
        configuration.arithmetic boundaryEqual _
    _ = encodeFinalPhysical configuration
        (HTFFT.Fixed.layeredSuffix configuration.arithmetic.fixedConfig table
          configuration.prefixBoundary (decodePrefix configuration input)) := by
      unfold encodeFinalPhysical HTFFT.Fixed.layeredSuffix resultValueThrough
      rw [stagesThrough_last configuration nonempty]
    _ = FFTStageChain.resultFrame configuration table input := rfl

private theorem functionThrough_last_cast
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (nonempty : stageCount depth configuration ≠ 0) :
    (fun frame cycle =>
      castObservation
        (lastOutputData_eq_parentOutputData configuration nonempty)
        (functionThrough configuration table
          (lastIndex configuration nonempty) frame cycle)) =
      chainFunction configuration table := by
  funext frame cycle
  apply Prod.ext
  · rfl
  · exact congrFun
      (resultFrameThrough_last_cast configuration table nonempty
        (fun inputCycle => (frame inputCycle).2)) cycle

private theorem resultFrame_empty_cast
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (empty : stageCount depth configuration = 0)
    (input : PrefixFrame configuration) :
    (fun cycle =>
      Eq.mp (parentInputData_eq_parentOutputData_of_empty configuration empty)
        (input cycle)) =
      FFTStageChain.resultFrame configuration table input := by
  let boundaryEqual :=
    prefixGeometry_eq_finalGeometry_of_empty configuration empty
  have framesEqual :
      (fun cycle =>
        Eq.mp
          (parentInputData_eq_parentOutputData_of_empty configuration empty)
          (input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input := by
    funext cycle
    rw [FFTStage.castBoundaryFrame_apply]
    have cycleEqual :
        Fin.cast
            (congrArg FFTStage.BoundaryGeometry.frameLength
              boundaryEqual).symm cycle = cycle := by
      apply Fin.ext
      rfl
    rw [cycleEqual]
    have dataProof :
        parentInputData_eq_parentOutputData_of_empty configuration empty =
          congrArg (FFTStage.BoundaryData configuration.arithmetic)
            boundaryEqual := Subsingleton.elim _ _
    rw [dataProof]
    exact (FFTStage.castBoundaryData_eq_mp configuration.arithmetic
      boundaryEqual (input cycle)).symm
  have suffixEmpty :
      HTFFT.Exact.butterflyStageSuffix depth
          configuration.prefixBoundary = [] := by
    unfold HTFFT.Exact.butterflyStageSuffix
    apply List.drop_eq_nil_iff.mpr
    simp only [HTFFT.Exact.butterflyStages, List.length_finRange]
    change depth - configuration.laneDepth = 0 at empty
    omega
  calc
    (fun cycle =>
      Eq.mp (parentInputData_eq_parentOutputData_of_empty configuration empty)
        (input cycle)) =
        FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
          input := framesEqual
    _ = FFTStage.castBoundaryFrame configuration.arithmetic boundaryEqual
        (FFTStage.encodeBoundaryFrame configuration.arithmetic
          configuration.prefixGeometry
          (FFTStage.decodeBoundaryFrame configuration.arithmetic
            configuration.prefixGeometry input)) := by
      rw [FFTStage.encodeBoundaryFrame_decodeBoundaryFrame]
    _ = FFTStage.encodeBoundaryFrame configuration.arithmetic
        configuration.finalGeometry (decodePrefix configuration input) := by
      exact FFTStage.castBoundaryFrame_encodeBoundaryFrame
        configuration.arithmetic boundaryEqual _
    _ = FFTStageChain.resultFrame configuration table input := by
      unfold FFTStageChain.resultFrame FFTStageChain.resultValue
        encodeFinalPhysical HTFFT.Fixed.layeredSuffix
      rw [suffixEmpty]
      rfl

private theorem function_empty_cast
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (empty : stageCount depth configuration = 0) :
    (fun frame cycle =>
      castObservation
        (parentInputData_eq_parentOutputData_of_empty configuration empty)
        (frame cycle)) =
      chainFunction configuration table := by
  funext frame cycle
  apply Prod.ext
  · rfl
  · exact congrFun
      (resultFrame_empty_cast configuration table empty
        (fun inputCycle => (frame inputCycle).2)) cycle

/-- The unresolved family body computes the public chain function with the
sum of the latencies supplied by its child contracts. -/
private theorem chainComputation
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic table
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index))) :
    FramedLatency.Computes configuration.frameLength
      (FFTStageChain.accumulatedLatency configuration stageLatency)
      configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStageChain.OutputObservation configuration =>
        output.1 = true)
      (chainFunction configuration table)
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      (trace.parent.outputs.map
        (FFTStageChain.outputObservation configuration)) := by
  by_cases empty : stageCount depth configuration = 0
  · have identity := FramedLatency.computes_id
      (frameLength := configuration.frameLength)
      (positive := configuration.frameLength_pos)
      (isFirst := fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
    have preservesFirst : ∀ output :
        FFTStageChain.InputObservation configuration,
        (castObservation
            (parentInputData_eq_parentOutputData_of_empty configuration empty)
            output).1 = true ↔ output.1 = true := by
      intro output
      rfl
    have exposed := FramedLatency.computes_map_outputs
      (mappedOutputFirst := fun output :
        FFTStageChain.OutputObservation configuration => output.1 = true)
      (castObservation
        (parentInputData_eq_parentOutputData_of_empty configuration empty))
      preservesFirst identity
    simp only [List.map_map] at exposed
    have exposedOutputs :
        trace.parent.inputs.map
            (castObservation
              (parentInputData_eq_parentOutputData_of_empty configuration empty) ∘
              FFTStageChain.inputObservation configuration) =
          trace.parent.outputs.map
            (FFTStageChain.outputObservation configuration) := by
      simpa only [Function.comp_def] using
        (parentOutputs_eq_parentInputs_of_empty configuration table trace
          wiring empty).symm
    rw [exposedOutputs] at exposed
    have zeroLatency :
        FFTStageChain.accumulatedLatency configuration stageLatency = 0 := by
      have noStages :
          List.finRange (stageCount depth configuration) = [] :=
        List.finRange_eq_nil_iff.mpr empty
      simp [FFTStageChain.accumulatedLatency, noStages]
    rw [zeroLatency]
    change FramedLatency.Computes configuration.frameLength 0
      configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStageChain.OutputObservation configuration =>
        output.1 = true)
      (fun frame cycle =>
        castObservation
          (parentInputData_eq_parentOutputData_of_empty configuration empty)
          (frame cycle))
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      (trace.parent.outputs.map
        (FFTStageChain.outputObservation configuration)) at exposed
    rw [function_empty_cast configuration table empty] at exposed
    exact exposed
  · let last := lastIndex configuration empty
    have through := computationThrough configuration table stageLatency trace
      wiring stageCorrect last
    have preservesFirst : ∀ output :
        FFTStage.OutputObservation configuration.arithmetic
          (stageGeometry configuration last),
        (castObservation
            (lastOutputData_eq_parentOutputData configuration empty)
            output).1 = true ↔ output.1 = true := by
      intro output
      rfl
    have exposed := FramedLatency.computes_map_outputs
      (mappedOutputFirst := fun output :
        FFTStageChain.OutputObservation configuration => output.1 = true)
      (castObservation
        (lastOutputData_eq_parentOutputData configuration empty))
      preservesFirst through
    simp only [List.map_map] at exposed
    have exposedOutputs :
        (trace.child (.stage last)).outputs.map
            (castObservation
              (lastOutputData_eq_parentOutputData configuration empty) ∘
              FFTStage.outputObservation configuration.arithmetic
                (stageGeometry configuration last)) =
          trace.parent.outputs.map
            (FFTStageChain.outputObservation configuration) := by
      simpa only [Function.comp_def] using
        (parentOutputs_eq_lastOutputs configuration table trace wiring empty).symm
    rw [exposedOutputs] at exposed
    rw [latencyThrough_last configuration stageLatency empty] at exposed
    change FramedLatency.Computes configuration.frameLength
      (FFTStageChain.accumulatedLatency configuration stageLatency)
      configuration.frameLength_pos
      (fun input : FFTStageChain.InputObservation configuration =>
        input.1 = true)
      (fun output : FFTStageChain.OutputObservation configuration =>
        output.1 = true)
      (fun frame cycle =>
        castObservation
          (lastOutputData_eq_parentOutputData configuration empty)
          (functionThrough configuration table last frame cycle))
      (trace.parent.inputs.map
        (FFTStageChain.inputObservation configuration))
      (trace.parent.outputs.map
        (FFTStageChain.outputObservation configuration)) at exposed
    rw [functionThrough_last_cast configuration table empty] at exposed
    exact exposed

/-- The permanent rolled-stage body satisfies its public chain contract when
each unresolved stage satisfies its public contract and their proposed
latencies sum to the latency declared by the chain configuration. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (FFTStageChain.body depth configuration table).Trace)
    (wiring : trace.WiringHolds)
    (latencyMatches :
      FFTStageChain.accumulatedLatency configuration stageLatency =
        configuration.stageChainLatency)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic table
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index))) :
    FFTStageChain.contract configuration table trace.parent := by
  have computation := chainComputation configuration table stageLatency trace
    wiring stageCorrect
  rw [latencyMatches] at computation
  have relation :
      FramedLatency.Relates configuration.frameLength
        configuration.stageChainLatency configuration.frameLength_pos
        (fun input : FFTStageChain.InputObservation configuration =>
          input.1 = true)
        (fun output : FFTStageChain.OutputObservation configuration =>
          output.1 = true)
        (FFTStageChain.carriedRelation configuration table)
        (trace.parent.inputs.map
          (FFTStageChain.inputObservation configuration))
        (trace.parent.outputs.map
          (FFTStageChain.outputObservation configuration)) := by
    exact FramedLatency.mono computation (fun input output equal => by
      unfold FFTStageChain.carriedRelation
      rw [equal]
      rfl)
  unfold FFTStageChain.contract FFTStageChain.frameRelation
  exact FramedLatency.holds_of_relates_projection
    (inputFirst := fun input : FFTStageChain.InputObservation configuration =>
      input.1 = true)
    (outputFirst := fun output : FFTStageChain.OutputObservation configuration =>
      output.1 = true)
    (relation := FFTStageChain.carriedRelation configuration table)
    (FFTStageChain.inputObservation configuration)
    (FFTStageChain.outputObservation configuration)
    relation

end HTFFT.Silean.FFT.FFTStageChain.Internal
