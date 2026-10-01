import HTFFT.Silean.FFTStageLane.Internal.FFTStageLaneStep
import Silean.Semantics.StructuralObservation

/-! Trace correctness of one physical rolled-stage lane. -/

namespace HTFFT.Silean.FFTStageLane.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint

theorem contract_of_execution
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (FFTStageLane.twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (carrier : PipelinedFixedButterfly.ProductCarrierCoversData
      dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline).State}
    {inputs : List (FFTStageLane.ports dataFormat twiddleFormat
      phaseWidth).inputs.Values}
    {outputs : List (FFTStageLane.ports dataFormat twiddleFormat
      phaseWidth).outputs.Values}
    (execution :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        |>.Executes initialState inputs outputs finalState) :
    FFTStageLane.contract dataFormat twiddleFormat (2 ^ pairExponent)
      (Nat.two_pow_pos pairExponent) phaseWidth laneAddressWidth lane
      twiddleValues pipeline execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let firstExecution := observed.child .firstDelay
  let secondExecution := observed.child .secondDelay
  let butterflyExecution := observed.child .butterfly
  simp only [structuralChildren] at firstExecution secondExecution butterflyExecution

  have firstContract := ShiftRegister.contract_of_execution
    (FFTStageLane.dataSignalType dataFormat) (2 ^ pairExponent)
    (Nat.two_pow_pos pairExponent) firstExecution
  have secondContract := ShiftRegister.contract_of_execution
    (FFTStageLane.dataSignalType dataFormat) (2 ^ pairExponent)
    (Nat.two_pow_pos pairExponent) secondExecution
  have butterflyContract := PipelinedFixedButterfly.contract_of_execution
    dataFormat twiddleFormat pipeline carrier butterflyExecution

  let firstOutputs : List (FFTStageLane.Value dataFormat) :=
    (hierarchy.map (fun step => (step.children .firstDelay).outputs)).map
      (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output)
  let secondOutputs : List (FFTStageLane.Value dataFormat) :=
    (hierarchy.map (fun step => (step.children .secondDelay).outputs)).map
      (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output)
  let invocations : List (FFTStageLane.Invocation phaseWidth dataFormat) :=
    hierarchy.map (fun step => FFTStageLane.invocationValue dataFormat
      twiddleFormat phaseWidth step.inputs
      ((fun output : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output) (step.children .firstDelay).outputs)
      ((fun output : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output) (step.children .secondDelay).outputs))
  have secondInputsEq :
      FFTStageLane.secondDelayInputs dataFormat twiddleFormat phaseWidth
          inputs secondOutputs =
        (hierarchy.map (fun step => (step.children .secondDelay).inputs)).map
          (fun input : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).inputs.Values =>
            input .input) := by
    rw [← observed.hierarchy_inputs]
    unfold secondOutputs
    rw [List.map_map, FFTStageLane.secondDelayInputs_map]
    rw [List.map_map]
    apply List.map_congr_left
    intro step member
    have wired := secondDelayInput_of_solution
      (observed.solution_of_mem step member)
    exact wired.symm

  have invocationsEq :
      FFTStageLane.invocationsOf dataFormat twiddleFormat phaseWidth
          inputs firstOutputs secondOutputs = invocations := by
    rw [← observed.hierarchy_inputs]
    unfold firstOutputs secondOutputs invocations
    rw [List.map_map, List.map_map]
    exact FFTStageLane.invocationsOf_map dataFormat twiddleFormat phaseWidth
      hierarchy HierStep.inputs
        ((fun output : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
          output .output) ∘ fun step =>
            (step.children .firstDelay).outputs)
        ((fun output : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
          output .output) ∘ fun step =>
            (step.children .secondDelay).outputs)

  have firstInputsEq :
      inputs.map (FFTStageLane.firstDelayInput dataFormat twiddleFormat
          phaseWidth) =
        (hierarchy.map (fun step => (step.children .firstDelay).inputs)).map
          (fun input : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).inputs.Values =>
            input .input) := by
    rw [← observed.hierarchy_inputs, List.map_map]
    rw [List.map_map]
    apply List.map_congr_left
    intro step member
    exact (firstDelayInput_of_solution
      (observed.solution_of_mem step member)).symm

  have firstProjected := FixedLatency.computes_of_holds_projection
    (function := id)
    (fun input : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).inputs.Values => input .input)
    (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
      output .output) firstContract
  have secondProjected := FixedLatency.computes_of_holds_projection
    (function := id)
    (fun input : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).inputs.Values => input .input)
    (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
      output .output) secondContract
  have firstProjected' : FixedLatency.Computes (2 ^ pairExponent) id
      ((hierarchy.map (fun step => (step.children .firstDelay).inputs)).map
        (fun input : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).inputs.Values => input .input))
      firstOutputs := by
    unfold firstOutputs
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at firstProjected
    convert firstProjected using 1 <;> rfl
  have secondProjected' : FixedLatency.Computes (2 ^ pairExponent) id
      ((hierarchy.map (fun step => (step.children .secondDelay).inputs)).map
        (fun input : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).inputs.Values => input .input))
      secondOutputs := by
    unfold secondOutputs
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at secondProjected
    convert secondProjected using 1 <;> rfl

  unfold FFTStageLane.contract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  refine ⟨firstOutputs, secondOutputs, invocations, ?_, ?_,
    invocationsEq.symm, ?_⟩
  · have mapped := FixedLatency.computes_congr_inputs firstInputsEq.symm
      firstProjected'
    have exposed := FixedLatency.computes_map_inputs
      (FFTStageLane.firstDelayInput dataFormat twiddleFormat phaseWidth) mapped
    simpa only [Function.comp_def, id_eq] using exposed
  · exact FixedLatency.computes_congr_inputs secondInputsEq.symm secondProjected'
  · unfold FixedLatency.Relates
    constructor
    · rw [execution.length_eq, ← observed.length_eq]
      simp only [invocations, List.length_map]
    · intro t invocationInTrace outputInTrace
      have sourceInHierarchy : t < hierarchy.length := by
        simpa [invocations] using invocationInTrace
      have finalInHierarchy : t + pipeline.latency < hierarchy.length := by
        rw [observed.length_eq, ← execution.length_eq]
        exact outputInTrace
      have butterflyAt := FixedLatency.relation_at_of_trace
        butterflyExecution butterflyContract t
        (by simpa using sourceInHierarchy)
        (by simpa using finalInHierarchy)
      simp only [List.get_eq_getElem, List.getElem_map] at butterflyAt
      let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
      let finalStep := hierarchy.get
        ⟨t + pipeline.latency, finalInHierarchy⟩
      have sourceSolution := observed.solution_at t sourceInHierarchy
      have finalSolution := observed.solution_at
        (t + pipeline.latency) finalInHierarchy
      have operands := butterflyOperands_of_solution sourceSolution
      have twiddle := butterflyTwiddle_of_solution sourceSolution
      have parentOutputs := parentOutputs_of_solution finalSolution
      have finalAt := observed.output_at rootOutputs
        (t + pipeline.latency) finalInHierarchy outputInTrace
      change
        (finalStep.children .butterfly).outputs .upper =
            PipelinedFixedButterfly.encodeComplex
              (PipelinedFixedButterfly.outputComponentWidth dataFormat)
              (PipelinedFixedButterfly.resultValue dataFormat twiddleFormat
                ((sourceStep.children .butterfly).inputs .a)
                ((sourceStep.children .butterfly).inputs .b)
                ((sourceStep.children .butterfly).inputs .twiddle)).upper ∧
          (finalStep.children .butterfly).outputs .lower =
            PipelinedFixedButterfly.encodeComplex
              (PipelinedFixedButterfly.outputComponentWidth dataFormat)
              (PipelinedFixedButterfly.resultValue dataFormat twiddleFormat
                ((sourceStep.children .butterfly).inputs .a)
                ((sourceStep.children .butterfly).inputs .b)
                ((sourceStep.children .butterfly).inputs .twiddle)).lower
        at butterflyAt
      rw [operands.1, operands.2, twiddle] at butterflyAt
      rw [← finalAt]
      unfold FFTStageLane.outputRelation FFTStageLane.resultValue
      rw [parentOutputs.1, parentOutputs.2]
      simpa [invocations, sourceStep, finalStep,
        FFTStageLane.invocationValue] using butterflyAt

/-- The two physical register chains of a lane admit synchronized abstract
delay-line traces.  This is a structural-refinement witness used by the
parent stage; unlike the natural lane contract, it deliberately exposes only
existential abstract endpoint states. -/
theorem delayTraces_of_execution
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (FFTStageLane.twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (carrier : PipelinedFixedButterfly.ProductCarrierCoversData
      dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline).State}
    {inputs : List (FFTStageLane.ports dataFormat twiddleFormat
      phaseWidth).inputs.Values}
    {outputs : List (FFTStageLane.ports dataFormat twiddleFormat
      phaseWidth).outputs.Values}
    (execution :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        |>.Executes initialState inputs outputs finalState) :
    ∃ firstInitial firstFinal secondInitial secondFinal firstOutputs secondOutputs,
      Trace (_root_.Silean.DelayLine.Step (2 ^ pairExponent)) firstInitial
          (inputs.map (FFTStageLane.firstDelayInput dataFormat twiddleFormat
            phaseWidth)) firstOutputs firstFinal ∧
        Trace (_root_.Silean.DelayLine.Step (2 ^ pairExponent)) secondInitial
          (FFTStageLane.secondDelayInputs dataFormat twiddleFormat phaseWidth
            inputs secondOutputs) secondOutputs secondFinal ∧
        firstOutputs.length = inputs.length ∧
        secondOutputs.length = inputs.length ∧
        FixedLatency.Relates pipeline.latency
          (FFTStageLane.outputRelation dataFormat twiddleFormat phaseWidth
            laneAddressWidth lane twiddleValues)
          (FFTStageLane.invocationsOf dataFormat twiddleFormat phaseWidth
            inputs firstOutputs secondOutputs) outputs := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let firstExecution := observed.child .firstDelay
  let secondExecution := observed.child .secondDelay
  let butterflyExecution := observed.child .butterfly
  simp only [structuralChildren] at firstExecution secondExecution butterflyExecution
  obtain ⟨firstInitial, firstFinal, firstTrace⟩ :=
    ShiftRegister.delayTrace_of_execution
      (FFTStageLane.dataSignalType dataFormat) (2 ^ pairExponent)
      (Nat.two_pow_pos pairExponent) firstExecution
  obtain ⟨secondInitial, secondFinal, secondTrace⟩ :=
    ShiftRegister.delayTrace_of_execution
      (FFTStageLane.dataSignalType dataFormat) (2 ^ pairExponent)
      (Nat.two_pow_pos pairExponent) secondExecution
  have butterflyContract := PipelinedFixedButterfly.contract_of_execution
    dataFormat twiddleFormat pipeline carrier butterflyExecution
  let firstOutputs : List (FFTStageLane.Value dataFormat) :=
    (hierarchy.map (fun step => (step.children .firstDelay).outputs)).map
      (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output)
  let secondOutputs : List (FFTStageLane.Value dataFormat) :=
    (hierarchy.map (fun step => (step.children .secondDelay).outputs)).map
      (fun output : (ShiftRegister.ports
        (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output)
  let invocations : List (FFTStageLane.Invocation phaseWidth dataFormat) :=
    hierarchy.map (fun step => FFTStageLane.invocationValue dataFormat
      twiddleFormat phaseWidth step.inputs
      ((fun output : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output) (step.children .firstDelay).outputs)
      ((fun output : (ShiftRegister.ports
          (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
        output .output) (step.children .secondDelay).outputs))
  have firstInputsEq :
      inputs.map (FFTStageLane.firstDelayInput dataFormat twiddleFormat
          phaseWidth) =
        (hierarchy.map (fun step => (step.children .firstDelay).inputs)).map
          (fun input : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).inputs.Values =>
            input .input) := by
    rw [← observed.hierarchy_inputs, List.map_map, List.map_map]
    apply List.map_congr_left
    intro step member
    exact (firstDelayInput_of_solution
      (observed.solution_of_mem step member)).symm
  have secondInputsEq :
      FFTStageLane.secondDelayInputs dataFormat twiddleFormat phaseWidth
          inputs secondOutputs =
        (hierarchy.map (fun step => (step.children .secondDelay).inputs)).map
          (fun input : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).inputs.Values =>
            input .input) := by
    rw [← observed.hierarchy_inputs]
    unfold secondOutputs
    rw [List.map_map, FFTStageLane.secondDelayInputs_map, List.map_map]
    apply List.map_congr_left
    intro step member
    exact (secondDelayInput_of_solution
      (observed.solution_of_mem step member)).symm
  have invocationsEq :
      FFTStageLane.invocationsOf dataFormat twiddleFormat phaseWidth
          inputs firstOutputs secondOutputs = invocations := by
    rw [← observed.hierarchy_inputs]
    unfold firstOutputs secondOutputs invocations
    rw [List.map_map, List.map_map]
    exact FFTStageLane.invocationsOf_map dataFormat twiddleFormat phaseWidth
      hierarchy HierStep.inputs
        ((fun output : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
          output .output) ∘ fun step =>
            (step.children .firstDelay).outputs)
        ((fun output : (ShiftRegister.ports
            (FFTStageLane.dataSignalType dataFormat)).outputs.Values =>
          output .output) ∘ fun step =>
            (step.children .secondDelay).outputs)
  have firstOutputsLength : firstOutputs.length = inputs.length := by
    unfold firstOutputs
    rw [List.length_map, List.length_map, observed.length_eq]
  have secondOutputsLength : secondOutputs.length = inputs.length := by
    unfold secondOutputs
    rw [List.length_map, List.length_map, observed.length_eq]
  refine ⟨firstInitial, firstFinal, secondInitial, secondFinal,
    firstOutputs, secondOutputs, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [firstOutputs] using
      (firstInputsEq ▸ firstTrace)
  · simpa only [secondOutputs] using
      (secondInputsEq ▸ secondTrace)
  · exact firstOutputsLength
  · exact secondOutputsLength
  · rw [invocationsEq]
    unfold FixedLatency.Relates
    constructor
    · rw [execution.length_eq, ← observed.length_eq]
      simp only [invocations, List.length_map]
    · intro t invocationInTrace outputInTrace
      have sourceInHierarchy : t < hierarchy.length := by
        simpa [invocations] using invocationInTrace
      have finalInHierarchy : t + pipeline.latency < hierarchy.length := by
        rw [observed.length_eq, ← execution.length_eq]
        exact outputInTrace
      have butterflyAt := FixedLatency.relation_at_of_trace
        butterflyExecution butterflyContract t
        (by simpa using sourceInHierarchy)
        (by simpa using finalInHierarchy)
      simp only [List.get_eq_getElem, List.getElem_map] at butterflyAt
      let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
      let finalStep := hierarchy.get
        ⟨t + pipeline.latency, finalInHierarchy⟩
      have sourceSolution := observed.solution_at t sourceInHierarchy
      have finalSolution := observed.solution_at
        (t + pipeline.latency) finalInHierarchy
      have operands := butterflyOperands_of_solution sourceSolution
      have twiddle := butterflyTwiddle_of_solution sourceSolution
      have parentOutputs := parentOutputs_of_solution finalSolution
      have finalAt := observed.output_at rootOutputs
        (t + pipeline.latency) finalInHierarchy outputInTrace
      change
        (finalStep.children .butterfly).outputs .upper =
            PipelinedFixedButterfly.encodeComplex
              (PipelinedFixedButterfly.outputComponentWidth dataFormat)
              (PipelinedFixedButterfly.resultValue dataFormat twiddleFormat
                ((sourceStep.children .butterfly).inputs .a)
                ((sourceStep.children .butterfly).inputs .b)
                ((sourceStep.children .butterfly).inputs .twiddle)).upper ∧
          (finalStep.children .butterfly).outputs .lower =
            PipelinedFixedButterfly.encodeComplex
              (PipelinedFixedButterfly.outputComponentWidth dataFormat)
              (PipelinedFixedButterfly.resultValue dataFormat twiddleFormat
                ((sourceStep.children .butterfly).inputs .a)
                ((sourceStep.children .butterfly).inputs .b)
                ((sourceStep.children .butterfly).inputs .twiddle)).lower
        at butterflyAt
      rw [operands.1, operands.2, twiddle] at butterflyAt
      rw [← finalAt]
      unfold FFTStageLane.outputRelation FFTStageLane.resultValue
      rw [parentOutputs.1, parentOutputs.2]
      simpa [invocations, sourceStep, finalStep,
        FFTStageLane.invocationValue] using butterflyAt

end HTFFT.Silean.FFTStageLane.Internal
