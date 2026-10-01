import Silean.Modules.BarrelShifter.Internal.BarrelShifterArithmetic
import Silean.Modules.BarrelShifter.Internal.BarrelShifterStep
import Silean.Semantics.StructuralObservation

/-! Trace correctness of the structural logarithmic mux network. -/

namespace Silean.Modules.BarrelShifter.Internal

open Silean
open Silean.Modules

/-- Every structural execution satisfies the natural fixed-latency rotation
contract. -/
theorem contract_of_execution (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent)
    {initialState finalState :
      (Modules.BarrelShifter.moduleStructure element exponent pipeline).State}
    {inputs : List (ports element exponent).inputs.Values}
    {outputs : List (ports element exponent).outputs.Values}
    (execution : (Modules.BarrelShifter.moduleStructure
      element exponent pipeline).Executes
        initialState inputs outputs finalState) :
    contract element exponent pipeline execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let parentInputs : List (Payload element exponent) := hierarchy.map fun step =>
    (step.inputs .shift, step.inputs .data)
  let parentOutputs := hierarchy.map fun step => step.outputs .result
  let stageInputs (stage : Fin exponent) : List (Payload element exponent) :=
    hierarchy.map fun step =>
      ((step.children (.stage stage)).inputs .shift,
        (step.children (.stage stage)).inputs .data)
  let stageOutputs (stage : Fin exponent) : List (Payload element exponent) :=
    hierarchy.map fun step =>
      ((step.children (.stage stage)).outputs .shift,
        (step.children (.stage stage)).outputs .result)
  let boundaryValues (boundary : Fin (exponent + 1)) :
      List (Payload element exponent) :=
    if zero : boundary.val = 0 then parentInputs
    else stageOutputs (stageBeforeBoundary exponent boundary zero)
  let outputDelayInputs :
      List (Fin (size exponent) → element.Denote) := hierarchy.map fun step =>
    (step.children .outputDelay).inputs .input
  let outputDelayOutputs :
      List (Fin (size exponent) → element.Denote) := hierarchy.map fun step =>
    (step.children .outputDelay).outputs .output

  have stageComputation (stage : Fin exponent) :
      FixedLatency.Computes
        (pipeline.registerBoundary stage.castSucc).toNat
        (stageFunction exponent stage)
        (stageInputs stage) (stageOutputs stage) := by
    have childExecution := observed.child (.stage stage)
    have childContract := Stage.contract_of_execution element exponent stage
      (pipeline.registerBoundary stage.castSucc) childExecution
    unfold Stage.contract at childContract
    have projected := FixedLatency.computes_of_holds_projection
      (function := stageFunction exponent stage)
      (fun input : (Stage.ports element exponent).inputs.Values =>
        (input .shift, input .data))
      (fun output : (Stage.ports element exponent).outputs.Values =>
        (output .shift, output .result))
      childContract
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at projected
    change FixedLatency.Computes
      (pipeline.registerBoundary stage.castSucc).toNat
      (stageFunction exponent stage)
      ((hierarchy.map fun step =>
        (step.children (.stage stage)).inputs).map
          (fun input => (input .shift, input .data)))
      ((hierarchy.map fun step =>
        (step.children (.stage stage)).outputs).map
          (fun output => (output .shift, output .result))) at projected
    rw [List.map_map, List.map_map] at projected
    exact projected

  have outputDelayComputation :
      FixedLatency.Computes
        (pipeline.registerBoundary (Fin.last exponent)).toNat id
        outputDelayInputs outputDelayOutputs := by
    have childExecution := observed.child .outputDelay
    have childContract := OptionalShiftRegister.contract_of_execution
      (.vector (size exponent) element)
      (pipeline.registerBoundary (Fin.last exponent)).toNat childExecution
    unfold OptionalShiftRegister.contract at childContract
    have projected := FixedLatency.computes_of_holds_projection
      (function := id)
      (fun input : (OptionalShiftRegister.ports
        (.vector (size exponent) element)).inputs.Values => input .input)
      (fun output : (OptionalShiftRegister.ports
        (.vector (size exponent) element)).outputs.Values => output .output)
      childContract
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at projected
    change FixedLatency.Computes
      (pipeline.registerBoundary (Fin.last exponent)).toNat id
      ((hierarchy.map fun step =>
        (step.children .outputDelay).inputs).map (fun input => input .input))
      ((hierarchy.map fun step =>
        (step.children .outputDelay).outputs).map (fun output => output .output))
      at projected
    rw [List.map_map, List.map_map] at projected
    exact projected

  have boundaryValues_castSucc (stage : Fin exponent) :
      boundaryValues stage.castSucc =
        if zero : stage.val = 0 then parentInputs
        else stageOutputs (previousStage exponent stage) := by
    unfold boundaryValues
    by_cases zero : stage.val = 0
    · rw [dif_pos zero, dif_pos (by simpa using zero)]
    · rw [dif_neg zero, dif_neg (by simpa using zero)]
      congr 1

  have stageInputsEqual (stage : Fin exponent) :
      stageInputs stage = boundaryValues stage.castSucc := by
    rw [boundaryValues_castSucc]
    unfold stageInputs
    by_cases zero : stage.val = 0
    · rw [dif_pos zero]
      unfold parentInputs
      apply List.map_congr_left
      intro step member
      have equation := stageInput_of_solution
        (observed.solution_of_mem step member) stage
      rw [dif_pos zero] at equation
      exact equation
    · rw [dif_neg zero]
      unfold stageOutputs
      apply List.map_congr_left
      intro step member
      have equation := stageInput_of_solution
        (observed.solution_of_mem step member) stage
      rw [dif_neg zero] at equation
      exact equation

  have boundaryValues_succ (stage : Fin exponent) :
      boundaryValues stage.succ = stageOutputs stage := by
    unfold boundaryValues
    simp

  have outputDelayInputsEqual :
      outputDelayInputs =
        (boundaryValues (Fin.last exponent)).map Prod.snd := by
    by_cases empty : exponent = 0
    · have boundaryEqual :
          boundaryValues (Fin.last exponent) = parentInputs := by
        unfold boundaryValues
        rw [dif_pos (by simp [empty])]
      rw [boundaryEqual]
      unfold outputDelayInputs parentInputs
      rw [List.map_map]
      apply List.map_congr_left
      intro step member
      have equation := outputDelayInput_of_solution
        (observed.solution_of_mem step member)
      rw [dif_pos empty] at equation
      change (step.children .outputDelay).inputs .input =
        step.inputs .data at equation
      exact equation
    · have boundaryEqual :
          boundaryValues (Fin.last exponent) =
            stageOutputs (lastStage exponent empty) := by
        unfold boundaryValues
        rw [dif_neg (by simpa using empty)]
        congr 1
      rw [boundaryEqual]
      unfold outputDelayInputs stageOutputs
      rw [List.map_map]
      apply List.map_congr_left
      intro step member
      have equation := outputDelayInput_of_solution
        (observed.solution_of_mem step member)
      rw [dif_neg empty] at equation
      change (step.children .outputDelay).inputs .input =
        (step.children (.stage (lastStage exponent empty))).outputs .result
        at equation
      exact equation

  have finalOutputs : parentOutputs = outputDelayOutputs := by
    unfold parentOutputs outputDelayOutputs
    apply List.map_congr_left
    intro step member
    exact output_of_solution (observed.solution_of_mem step member)

  have boundaryPrefix (boundary : Fin (exponent + 1)) :
      FixedLatency.Computes (boundaryLatency pipeline boundary)
        (boundaryResult exponent boundary)
        parentInputs (boundaryValues boundary) := by
    induction boundary using Fin.induction with
    | zero =>
        rw [boundaryLatency_zero, boundaryResult_zero]
        simpa [boundaryValues] using FixedLatency.computes_id parentInputs
    | succ stage induction =>
        have currentStage := FixedLatency.computes_congr_inputs
          (stageInputsEqual stage) (stageComputation stage)
        have throughStage := FixedLatency.computes_serial induction currentStage
        have throughBoundary := FixedLatency.computes_congr_outputs
          (boundaryValues_succ stage).symm throughStage
        rw [boundaryLatency_succ, boundaryResult_succ]
        exact throughBoundary

  have completeBoundary := boundaryPrefix (Fin.last exponent)
  have dataPrefix := FixedLatency.computes_map_outputs completeBoundary Prod.snd
  have delay := FixedLatency.computes_congr_inputs outputDelayInputsEqual
    outputDelayComputation
  have complete := FixedLatency.computes_serial dataPrefix delay
  rw [boundaryLatency_final_add_output] at complete
  have completeResult :
      FixedLatency.Computes pipeline.latency
        (fun payload : Payload element exponent =>
          resultValue exponent payload.1 payload.2)
        parentInputs outputDelayOutputs := by
    unfold FixedLatency.Computes FixedLatency.Relates at complete ⊢
    constructor
    · exact complete.1
    · intro t inputInTrace outputInTrace
      have related := complete.2 t inputInTrace outputInTrace
      simpa only [Function.comp_apply, id_eq, boundaryResult_final] using related

  have parentInputsOriginal :
      parentInputs = inputs.map fun input => (input .shift, input .data) := by
    unfold parentInputs
    calc
      hierarchy.map (fun step => (step.inputs .shift, step.inputs .data)) =
          (hierarchy.map HierStep.inputs).map
            (fun input => (input .shift, input .data)) := by
        simp [List.map_map]
      _ = inputs.map (fun input => (input .shift, input .data)) :=
        congrArg (List.map fun input => (input .shift, input .data))
          observed.hierarchy_inputs
  have parentOutputsOriginal :
      parentOutputs = outputs.map fun output => output .result := by
    unfold parentOutputs
    calc
      hierarchy.map (fun step => step.outputs .result) =
          (hierarchy.map HierStep.outputs).map
            (fun output => output .result) := by
        simp [List.map_map]
      _ = outputs.map (fun output => output .result) :=
        congrArg (List.map fun output => output .result) rootOutputs

  rw [← finalOutputs, parentInputsOriginal, parentOutputsOriginal]
    at completeResult
  have projected := FixedLatency.computes_map_inputs
    (fun input : (ports element exponent).inputs.Values =>
      (input .shift, input .data)) completeResult
  unfold contract FixedLatency.Holds FixedLatency.Computes at *
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have mappedOutputInTrace :
        t + pipeline.latency <
          (outputs.map fun output => output .result).length := by
      simpa using outputInTrace
    have related := projected.2 t inputInTrace mappedOutputInTrace
    have outputAt :
        (outputs.map fun output => output .result).get
            ⟨t + pipeline.latency, mappedOutputInTrace⟩ =
          (outputs.get ⟨t + pipeline.latency, outputInTrace⟩) .result := by
      simp
    change
      (outputs.map fun output => output .result).get
          ⟨t + pipeline.latency, mappedOutputInTrace⟩ =
        resultValue exponent
          ((inputs.get ⟨t, inputInTrace⟩) .shift)
          ((inputs.get ⟨t, inputInTrace⟩) .data) at related
    rw [outputAt] at related
    exact related

end Silean.Modules.BarrelShifter.Internal
