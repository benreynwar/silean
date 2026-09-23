import HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTStep
import Silean.Semantics.StructuralObservation

/-! All-time trace correctness of the natural-order unrolled FFT. -/

namespace HTFFT.Silean.UnrolledFFT.Internal

open _root_.Silean

/-- Every structural execution satisfies the natural fixed-point FFT
contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration table).Executes
        initialState inputs outputs finalState) :
    contract configuration table execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let networkExecution := observed.child (.network)
  have networkContract := UnrolledFFTNetwork.contract_of_execution
    configuration table twiddleFits carrier networkExecution

  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have hierarchyLength : hierarchy.length = inputs.length :=
      observed.length_eq
    have sourceInHierarchy : t < hierarchy.length := by
      rw [hierarchyLength]
      exact inputInTrace
    have finalInHierarchy :
        t + configuration.networkLatency < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      exact outputInTrace

    let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
    let finalStep := hierarchy.get
      ⟨t + configuration.networkLatency, finalInHierarchy⟩
    have sourceSolution := observed.solution_at t sourceInHierarchy
    have finalSolution := observed.solution_at
      (t + configuration.networkLatency) finalInHierarchy
    have sourceAt := observed.input_at t sourceInHierarchy inputInTrace
    have finalAt := observed.output_at rootOutputs
      (t + configuration.networkLatency) finalInHierarchy outputInTrace
    change sourceStep.inputs = inputs.get ⟨t, inputInTrace⟩ at sourceAt
    change finalStep.outputs =
      outputs.get ⟨t + configuration.networkLatency, outputInTrace⟩
      at finalAt

    have networkAt := FixedLatency.relation_at_of_trace
      networkExecution networkContract t
      (by simpa [networkExecution] using sourceInHierarchy)
      (by simpa [networkExecution] using finalInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at networkAt
    change
      (finalStep.children .network).outputs .output =
        UnrolledFFTLayer.encodeVector
          (configuration.boundaryFormat (Fin.last depth))
          (UnrolledFFTNetwork.resultValue configuration table
            ((sourceStep.children .network).inputs .input)) at networkAt

    rw [networkInput_eq_bitReverse_of_solution sourceSolution] at networkAt
    rw [← finalAt, ← sourceAt, output_of_solution finalSolution]
    rw [networkAt]
    rfl

end HTFFT.Silean.UnrolledFFT.Internal
