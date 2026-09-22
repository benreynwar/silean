import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyStep
import Silean.Semantics.StructuralObservation

/-! All-time trace correctness of the structural complex multiplier. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

open _root_.Silean
open _root_.Silean.Modules

/-- Every structural execution satisfies the state-free fixed-latency
complex-product contract. -/
theorem contract_of_execution
    (leftWidth rightWidth discardedWidth : Nat) (pipeline : Pipeline)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth discardedWidth
        pipeline.multiplierLatency pipeline.registerBeforeRounding).State}
    {inputs : List
      (ports leftWidth rightWidth discardedWidth).inputs.Values}
    {outputs : List
      (ports leftWidth rightWidth discardedWidth).outputs.Values}
    (execution :
      (moduleStructure leftWidth rightWidth discardedWidth
        pipeline.multiplierLatency pipeline.registerBeforeRounding).Executes
          initialState inputs outputs finalState) :
    contract leftWidth rightWidth discardedWidth pipeline
      execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  have realRealExecution := observed.child (.realReal)
  have imagImagExecution := observed.child (.imagImag)
  have realImagExecution := observed.child (.realImag)
  have imagRealExecution := observed.child (.imagReal)
  have numeratorDelayExecution := observed.child (.numeratorDelay)
  simp only [structuralChildren] at realRealExecution imagImagExecution realImagExecution imagRealExecution numeratorDelayExecution

  have realRealContract := PipelinedSignedMultiply.contract_of_execution
    leftWidth rightWidth pipeline.multiplierLatency realRealExecution
  have imagImagContract := PipelinedSignedMultiply.contract_of_execution
    leftWidth rightWidth pipeline.multiplierLatency imagImagExecution
  have realImagContract := PipelinedSignedMultiply.contract_of_execution
    leftWidth rightWidth pipeline.multiplierLatency realImagExecution
  have imagRealContract := PipelinedSignedMultiply.contract_of_execution
    leftWidth rightWidth pipeline.multiplierLatency imagRealExecution
  have numeratorDelayContract := OptionalShiftRegister.contract_of_execution
    (.vector 2 (.vector (numeratorWidth leftWidth rightWidth) .bit))
    (Bool.toNat pipeline.registerBeforeRounding) numeratorDelayExecution

  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have hierarchyLength : hierarchy.length = inputs.length :=
      observed.length_eq
    have inputHierarchyInTrace : t < hierarchy.length := by
      rw [hierarchyLength]
      exact inputInTrace
    have productHierarchyInTrace :
        t + pipeline.multiplierLatency < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      unfold Pipeline.latency at outputInTrace
      omega
    have finalHierarchyInTrace :
        t + pipeline.latency < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      exact outputInTrace

    let inputStep := hierarchy.get ⟨t, inputHierarchyInTrace⟩
    let productStep := hierarchy.get
      ⟨t + pipeline.multiplierLatency, productHierarchyInTrace⟩
    let finalStep := hierarchy.get
      ⟨t + pipeline.latency, finalHierarchyInTrace⟩

    have inputSolution :=
      observed.solution_at t inputHierarchyInTrace
    have productSolution := observed.solution_at
      (t + pipeline.multiplierLatency) productHierarchyInTrace
    have finalSolution := observed.solution_at
      (t + pipeline.latency) finalHierarchyInTrace
    have inputAt := observed.input_at t inputHierarchyInTrace inputInTrace
    change inputStep.inputs = inputs.get ⟨t, inputInTrace⟩ at inputAt

    have realRealProduct := FixedLatency.relation_at_of_trace
      realRealExecution realRealContract t
      (by simpa using inputHierarchyInTrace)
      (by simpa using productHierarchyInTrace)
    have imagImagProduct := FixedLatency.relation_at_of_trace
      imagImagExecution imagImagContract t
      (by simpa using inputHierarchyInTrace)
      (by simpa using productHierarchyInTrace)
    have realImagProduct := FixedLatency.relation_at_of_trace
      realImagExecution realImagContract t
      (by simpa using inputHierarchyInTrace)
      (by simpa using productHierarchyInTrace)
    have imagRealProduct := FixedLatency.relation_at_of_trace
      imagRealExecution imagRealContract t
      (by simpa using inputHierarchyInTrace)
      (by simpa using productHierarchyInTrace)
    simp only [List.get_eq_getElem, List.getElem_map] at realRealProduct imagImagProduct realImagProduct imagRealProduct
    change (productStep.children .realReal).outputs .result =
      SignedMultiply.resultValue leftWidth rightWidth
        ((inputStep.children .realReal).inputs .left)
        ((inputStep.children .realReal).inputs .right) at realRealProduct
    change (productStep.children .imagImag).outputs .result =
      SignedMultiply.resultValue leftWidth rightWidth
        ((inputStep.children .imagImag).inputs .left)
        ((inputStep.children .imagImag).inputs .right) at imagImagProduct
    change (productStep.children .realImag).outputs .result =
      SignedMultiply.resultValue leftWidth rightWidth
        ((inputStep.children .realImag).inputs .left)
        ((inputStep.children .realImag).inputs .right) at realImagProduct
    change (productStep.children .imagReal).outputs .result =
      SignedMultiply.resultValue leftWidth rightWidth
        ((inputStep.children .imagReal).inputs .left)
        ((inputStep.children .imagReal).inputs .right) at imagRealProduct

    have realRealLeft := ModuleStructure.child_input inputSolution
      (.realReal) (.left)
    have realRealRight := ModuleStructure.child_input inputSolution
      (.realReal) (.right)
    have imagImagLeft := ModuleStructure.child_input inputSolution
      (.imagImag) (.left)
    have imagImagRight := ModuleStructure.child_input inputSolution
      (.imagImag) (.right)
    have realImagLeft := ModuleStructure.child_input inputSolution
      (.realImag) (.left)
    have realImagRight := ModuleStructure.child_input inputSolution
      (.realImag) (.right)
    have imagRealLeft := ModuleStructure.child_input inputSolution
      (.imagReal) (.left)
    have imagRealRight := ModuleStructure.child_input inputSolution
      (.imagReal) (.right)
    change (inputStep.children .realReal).inputs .left =
      inputStep.inputs .leftReal at realRealLeft
    change (inputStep.children .realReal).inputs .right =
      inputStep.inputs .rightReal at realRealRight
    change (inputStep.children .imagImag).inputs .left =
      inputStep.inputs .leftImag at imagImagLeft
    change (inputStep.children .imagImag).inputs .right =
      inputStep.inputs .rightImag at imagImagRight
    change (inputStep.children .realImag).inputs .left =
      inputStep.inputs .leftReal at realImagLeft
    change (inputStep.children .realImag).inputs .right =
      inputStep.inputs .rightImag at realImagRight
    change (inputStep.children .imagReal).inputs .left =
      inputStep.inputs .leftImag at imagRealLeft
    change (inputStep.children .imagReal).inputs .right =
      inputStep.inputs .rightReal at imagRealRight
    rw [realRealLeft, realRealRight, inputAt] at realRealProduct
    rw [imagImagLeft, imagImagRight, inputAt] at imagImagProduct
    rw [realImagLeft, realImagRight, inputAt] at realImagProduct
    rw [imagRealLeft, imagRealRight, inputAt] at imagRealProduct

    have numeratorInput := numeratorDelayInput_of_solution
      leftWidth rightWidth discardedWidth pipeline.multiplierLatency
      pipeline.registerBeforeRounding productSolution
    change (productStep.children .numeratorDelay).inputs .input =
      numeratorPairCircuitValue leftWidth rightWidth
        ((productStep.children .realReal).outputs .result)
        ((productStep.children .imagImag).outputs .result)
        ((productStep.children .realImag).outputs .result)
        ((productStep.children .imagReal).outputs .result) at numeratorInput

    have delayOutputInTrace :
        (t + pipeline.multiplierLatency) +
            Bool.toNat pipeline.registerBeforeRounding < hierarchy.length := by
      simpa [Pipeline.latency, Nat.add_assoc] using finalHierarchyInTrace
    have delayedNumerator := FixedLatency.relation_at_of_trace
      numeratorDelayExecution numeratorDelayContract
      (t + pipeline.multiplierLatency)
      (by simpa using productHierarchyInTrace)
      (by simpa using delayOutputInTrace)
    simp only [List.get_eq_getElem, List.getElem_map] at delayedNumerator
    change
      ((hierarchy.get ⟨(t + pipeline.multiplierLatency) +
          Bool.toNat pipeline.registerBeforeRounding,
          delayOutputInTrace⟩).children .numeratorDelay).outputs .output =
        ((hierarchy.get ⟨t + pipeline.multiplierLatency,
          productHierarchyInTrace⟩).children .numeratorDelay).inputs .input
      at delayedNumerator
    have delayedNumeratorNormalized :
        (finalStep.children .numeratorDelay).outputs .output =
          (productStep.children .numeratorDelay).inputs .input := by
      simpa [finalStep, productStep, Pipeline.latency, Nat.add_assoc] using
        delayedNumerator
    rw [numeratorInput] at delayedNumeratorNormalized

    have circuitOutputs := circuitOutputs_of_solution
      leftWidth rightWidth discardedWidth pipeline.multiplierLatency
      pipeline.registerBeforeRounding finalSolution
    change finalStep.outputs .resultReal =
          roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
            ((finalStep.children .numeratorDelay).outputs .output
              ⟨0, by omega⟩) ∧
        finalStep.outputs .resultImag =
          roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
            ((finalStep.children .numeratorDelay).outputs .output
              ⟨1, by omega⟩) at circuitOutputs
    have outputAt := observed.output_at rootOutputs
      (t + pipeline.latency) finalHierarchyInTrace outputInTrace
    change finalStep.outputs =
      outputs.get ⟨t + pipeline.latency, outputInTrace⟩ at outputAt
    have outputRealAt := congrFun outputAt .resultReal
    have outputImagAt := congrFun outputAt .resultImag

    constructor
    · rw [← outputRealAt, circuitOutputs.1, delayedNumeratorNormalized]
      change roundedRealCircuitValue leftWidth rightWidth discardedWidth
          ((productStep.children .realReal).outputs .result)
          ((productStep.children .imagImag).outputs .result) = _
      rw [realRealProduct, imagImagProduct]
      exact roundedRealCircuit_eq_resultValue leftWidth rightWidth
        discardedWidth
        (inputs.get ⟨t, inputInTrace⟩ .leftReal)
        (inputs.get ⟨t, inputInTrace⟩ .leftImag)
        (inputs.get ⟨t, inputInTrace⟩ .rightReal)
        (inputs.get ⟨t, inputInTrace⟩ .rightImag)
    · rw [← outputImagAt, circuitOutputs.2, delayedNumeratorNormalized]
      change roundedImagCircuitValue leftWidth rightWidth discardedWidth
          ((productStep.children .realImag).outputs .result)
          ((productStep.children .imagReal).outputs .result) = _
      rw [realImagProduct, imagRealProduct]
      exact roundedImagCircuit_eq_resultValue leftWidth rightWidth
        discardedWidth
        (inputs.get ⟨t, inputInTrace⟩ .leftReal)
        (inputs.get ⟨t, inputInTrace⟩ .leftImag)
        (inputs.get ⟨t, inputInTrace⟩ .rightReal)
        (inputs.get ⟨t, inputInTrace⟩ .rightImag)

end HTFFT.Silean.PipelinedSignedComplexMultiply.Internal
