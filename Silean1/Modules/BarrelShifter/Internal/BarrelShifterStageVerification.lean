import Silean.Modules.BarrelShifter.Internal.BarrelShifterStageStructural
import Silean.Semantics.StructuralObservation

/-! Structural-to-trace proof for one aligned pipeline stage. -/

namespace Silean.Modules.BarrelShifter.Internal.Stage

open Silean
open Silean.Modules

/-- The child inputs and parent outputs of one satisfying hierarchy step. -/
private theorem equations_of_solution
    {element : SignalType} {exponent : Nat} {stage : Fin exponent}
    {registerInput : Bool}
    {step : HierStep (BarrelShifterStage.moduleStructure
      element exponent stage registerInput)}
    (satisfies : (BarrelShifterStage.moduleStructure
      element exponent stage registerInput).IsSolution step) :
    (step.children .dataDelay).inputs .input = step.inputs .data ∧
    (step.children .shiftDelay).inputs .input = step.inputs .shift ∧
    step.outputs .shift = (step.children .shiftDelay).outputs .output ∧
    step.outputs .result =
      Level.resultValue exponent stage
        ((step.children .shiftDelay).outputs .output)
        ((step.children .dataDelay).outputs .output) := by
  have dataInput := ModuleStructure.child_input satisfies .dataDelay .input
  have shiftInput := ModuleStructure.child_input satisfies .shiftDelay .input
  have levelShift := ModuleStructure.child_input satisfies .level .shift
  have levelData := ModuleStructure.child_input satisfies .level .data
  have shiftOutput := ModuleStructure.parent_output satisfies .shift
  have resultOutput := ModuleStructure.parent_output satisfies .result
  have levelRealizes := ModuleStructure.child_realizes satisfies .level
  have levelResult := Level.result_of_realization element exponent stage (by
    simpa only [BarrelShifterStage.structuralChildren] using levelRealizes)

  change (step.children .dataDelay).inputs .input = step.inputs .data at dataInput
  change (step.children .shiftDelay).inputs .input = step.inputs .shift at shiftInput
  change (step.children .level).inputs .shift =
    (step.children .shiftDelay).outputs .output at levelShift
  change (step.children .level).inputs .data =
    (step.children .dataDelay).outputs .output at levelData
  change step.outputs .shift =
    (step.children .shiftDelay).outputs .output at shiftOutput
  change step.outputs .result = (step.children .level).outputs .result at resultOutput
  change (step.children .level).outputs .result =
    Level.resultValue exponent stage
      ((step.children .level).inputs .shift)
      ((step.children .level).inputs .data) at levelResult

  refine ⟨dataInput, shiftInput, shiftOutput, ?_⟩
  rw [resultOutput, levelResult, levelShift, levelData]

/-- Every concrete stage execution satisfies its natural aligned-delay
contract. -/
theorem contract_of_execution (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool)
    {initialState finalState :
      (BarrelShifterStage.moduleStructure
        element exponent stage registerInput).State}
    {inputs : List (ports element exponent).inputs.Values}
    {outputs : List (ports element exponent).outputs.Values}
    (execution : (BarrelShifterStage.moduleStructure
      element exponent stage registerInput).Executes
        initialState inputs outputs finalState) :
    contract element exponent stage registerInput execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let dataExecution := observed.child (.dataDelay)
  let shiftExecution := observed.child (.shiftDelay)
  have dataContract := OptionalShiftRegister.contract_of_execution
    (.vector (size exponent) element) registerInput.toNat dataExecution
  have shiftContract := OptionalShiftRegister.contract_of_execution
    (.vector exponent .bit) registerInput.toNat shiftExecution

  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have hierarchyLength : hierarchy.length = inputs.length := observed.length_eq
    have sourceInHierarchy : t < hierarchy.length := by
      rw [hierarchyLength]
      exact inputInTrace
    have finalInHierarchy : t + registerInput.toNat < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      exact outputInTrace

    let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
    let finalStep := hierarchy.get
      ⟨t + registerInput.toNat, finalInHierarchy⟩
    have sourceSolution := observed.solution_at t sourceInHierarchy
    have finalSolution := observed.solution_at
      (t + registerInput.toNat) finalInHierarchy
    have sourceAt := observed.input_at t sourceInHierarchy inputInTrace
    have finalAt := observed.output_at rootOutputs
      (t + registerInput.toNat) finalInHierarchy outputInTrace

    have dataAt := FixedLatency.relation_at_of_trace dataExecution
      dataContract t
      (by simpa [dataExecution] using sourceInHierarchy)
      (by simpa [dataExecution] using finalInHierarchy)
    have shiftAt := FixedLatency.relation_at_of_trace shiftExecution
      shiftContract t
      (by simpa [shiftExecution] using sourceInHierarchy)
      (by simpa [shiftExecution] using finalInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at dataAt shiftAt

    have sourceEquations := equations_of_solution sourceSolution
    have finalEquations := equations_of_solution finalSolution
    change
      (finalStep.children .dataDelay).outputs .output =
        (sourceStep.children .dataDelay).inputs .input at dataAt
    change
      (finalStep.children .shiftDelay).outputs .output =
        (sourceStep.children .shiftDelay).inputs .input at shiftAt
    change sourceStep.inputs = inputs.get ⟨t, inputInTrace⟩ at sourceAt
    change finalStep.outputs =
      outputs.get ⟨t + registerInput.toNat, outputInTrace⟩ at finalAt

    rw [← finalAt, ← sourceAt]
    apply Prod.ext
    · rw [finalEquations.2.2.1, shiftAt, sourceEquations.2.1]
    · rw [finalEquations.2.2.2, shiftAt, dataAt,
        sourceEquations.2.1, sourceEquations.1]

end Silean.Modules.BarrelShifter.Internal.Stage
