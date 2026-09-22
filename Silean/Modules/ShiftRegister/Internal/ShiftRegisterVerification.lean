import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.ShiftRegister.Internal.ShiftRegisterStructure
import Silean.Semantics.DelayLine
import Silean.Semantics.StructuralExecution

/-! Shared structural, dependency, and trace proofs for both shift-register
facades. -/

namespace Silean.Modules.ShiftRegisterImplementation

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (latency : Nat) for body signalType latency where
  delay (_stage : Fin latency) := Register.certification signalType

@[reducible] private def childRules (signalType : SignalType) (latency : Nat) :
    ModuleStructuralCertification.Layer.ChildRules (body signalType latency) :=
  Contracts.Cycle.Certification.Layer.childStructuralRules
    (body signalType latency) (childContracts signalType latency)

private abbrev delayOccurrence (signalType : SignalType) (latency : Nat)
    (stage : Fin latency) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body signalType latency) (childRules signalType latency) :=
  ⟨.delay stage, Primitives.RegisterRule.observe⟩

module_complete_schedule completeSchedule (signalType : SignalType)
    (latency : Nat) for body signalType latency
    with childRules signalType latency := from (
      (Enumeration.fin latency).values.map
        (delayOccurrence signalType latency))

theorem Internal.structuralCertification (signalType : SignalType)
    (latency : Nat) :
    ModuleStructuralCertification (moduleStructure signalType latency) :=
  (completeSchedule signalType latency).certifyComposite
    (structuralChildren signalType latency)
    (Contracts.Cycle.Certification.Layer.structuralChildren
      (certifiedChildren signalType latency))
    (certifiedChildren_moduleStructure signalType latency)

namespace Internal

private abbrev Value (signalType : SignalType) := signalType.Denote

private def physicalStage {latency : Nat} (index : Fin latency) : Fin latency :=
  ⟨latency - 1 - index.val, by omega⟩

private def stateCorresponds (signalType : SignalType) (latency : Nat)
    (state : Fin latency → Value signalType)
    (structuralState : (moduleStructure signalType latency).State) : Prop :=
  ∀ index,
    (Register.certification signalType).stateCorresponds
      (fun | .stored => state index)
      (structuralState (.delay (physicalStage index)))

private theorem stateCoverage (signalType : SignalType) (latency : Nat)
    (structuralState : (moduleStructure signalType latency).State) :
    ∃ state, stateCorresponds signalType latency state structuralState := by
  classical
  let contractState : (index : Fin latency) →
      (Register.cycleContract signalType).state.Values :=
    fun index => Classical.choose
      ((Register.certification signalType).hasCorrespondingState
        (structuralState (.delay (physicalStage index))))
  let state : Fin latency → Value signalType :=
    fun index => contractState index .stored
  refine ⟨state, fun index => ?_⟩
  have corresponds := Classical.choose_spec
    ((Register.certification signalType).hasCorrespondingState
      (structuralState (.delay (physicalStage index))))
  simpa only [state, contractState] using corresponds

private def inputValue (signalType : SignalType)
    (inputs : (ShiftRegister.ports signalType).inputs.Values) : Value signalType :=
  inputs .input

private theorem delayInput_of_solution (signalType : SignalType)
    (latency : Nat)
    {hierStep : HierStep (moduleStructure signalType latency)}
    (satisfies : (moduleStructure signalType latency).IsSolution hierStep)
    (stage : Fin latency) :
    (hierStep.children (.delay stage)).inputs .input =
      if _first : stage.val = 0 then
        hierStep.inputs .input
      else
        (hierStep.children (.delay ⟨stage.val - 1, by omega⟩)).outputs
          .output := by
  have equation := ModuleStructure.child_input satisfies (.delay stage) (.input)
  by_cases first : stage.val = 0
  · simpa [wiring, first, EndpointContext.instanceOutput, SignalSource.value]
      using equation
  · simpa [wiring, first, EndpointContext.instanceOutput, SignalSource.value]
      using equation

private theorem boundaryOutput_of_solution (signalType : SignalType)
    (latency : Nat)
    {hierStep : HierStep (moduleStructure signalType latency)}
    (satisfies : (moduleStructure signalType latency).IsSolution hierStep) :
    hierStep.outputs .output =
      if zero : latency = 0 then
        hierStep.inputs .input
      else
        (hierStep.children (.delay ⟨latency - 1, by omega⟩)).outputs
          .output := by
  have equation := ModuleStructure.parent_output satisfies (.output)
  by_cases zero : latency = 0
  · simpa [wiring, zero, EndpointContext.instanceOutput, SignalSource.value]
      using equation
  · simpa [wiring, zero, EndpointContext.instanceOutput, SignalSource.value]
      using equation

private theorem positiveOutputDetermines (signalType : SignalType)
    (latency : Nat) (positive : 0 < latency)
    (left right : HierStep (moduleStructure signalType latency))
    (leftSatisfies : (moduleStructure signalType latency).IsSolution left)
    (rightSatisfies : (moduleStructure signalType latency).IsSolution right)
    (statesEqual :
      HierStep.currentState (moduleStructure signalType latency) left =
        HierStep.currentState (moduleStructure signalType latency) right) :
    left.outputs .output = right.outputs .output := by
  let last : Fin latency := ⟨latency - 1, by omega⟩
  have leftBoundary := boundaryOutput_of_solution signalType latency leftSatisfies
  have rightBoundary := boundaryOutput_of_solution signalType latency rightSatisfies
  rw [dif_neg (by omega)] at leftBoundary rightBoundary
  have childStatesEqual :
      HierStep.currentState (Register.moduleStructure signalType)
          (left.children (.delay last)) =
        HierStep.currentState (Register.moduleStructure signalType)
          (right.children (.delay last)) :=
    congrFun statesEqual (.delay last)
  have registerRuleCertification :
      ModuleStructuralRuleCertification (Register.moduleStructure signalType)
        (Register.cycleContract signalType).structuralRules :=
    ((Register.certified signalType).structuralRuleCertification).transport
      (Register.certified_moduleStructure signalType)
  have leftChildRealizes :=
    ModuleStructure.child_isSolution leftSatisfies (.delay last)
  have rightChildRealizes :=
    ModuleStructure.child_isSolution rightSatisfies (.delay last)
  simp only [structuralChildren, Register.design, Register.designWith]
    at leftChildRealizes rightChildRealizes
  have childOutputEqual :=
    registerRuleCertification.determines Primitives.RegisterRule.observe
      (left.children (.delay last)) (right.children (.delay last))
      leftChildRealizes rightChildRealizes
      childStatesEqual
      (by
        intro inputLabel member
        change inputLabel ∈ ([] : List (Register.ports signalType).inputs.Label) at member
        simp at member)
      Primitives.SingleOutput.output (by
        change Primitives.SingleOutput.output ∈
          ([Primitives.SingleOutput.output] :
            List (Register.ports signalType).outputs.Label)
        simp)
  exact leftBoundary.trans (childOutputEqual.trans rightBoundary.symm)

theorem optionalRuleCertification (signalType : SignalType) (latency : Nat) :
    ModuleStructuralRuleCertification (moduleStructure signalType latency)
      (OptionalShiftRegister.rules signalType latency) where
  structural := structuralCertification signalType latency
  determines := by
    intro name left right leftSatisfies rightSatisfies statesEqual
      inputsAgree outputLabel outputMem
    cases name
    cases outputLabel
    by_cases zero : latency = 0
    · have inputEqual : left.inputs = right.inputs := by
        funext inputLabel
        cases inputLabel
        exact inputsAgree .input (by simp [zero])
      have equal := (structuralCertification signalType latency).hasAtMostOneSolution
        left right leftSatisfies rightSatisfies inputEqual statesEqual
      exact congrFun (congrArg HierStep.outputs equal) .output
    · exact positiveOutputDetermines signalType latency (by omega)
        left right leftSatisfies rightSatisfies statesEqual

theorem shiftRuleCertification (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency) :
    ModuleStructuralRuleCertification (moduleStructure signalType latency)
      (ShiftRegister.rules signalType latency positive) where
  structural := structuralCertification signalType latency
  determines := by
    intro name left right leftSatisfies rightSatisfies statesEqual
      _inputsAgree outputLabel outputMem
    cases name
    cases outputLabel
    exact positiveOutputDetermines signalType latency positive
      left right leftSatisfies rightSatisfies statesEqual

private theorem delayStep_of_solution (signalType : SignalType) (latency : Nat)
    (currentState : Fin latency → Value signalType)
    {hierStep : HierStep (moduleStructure signalType latency)}
    (corresponds : stateCorresponds signalType latency currentState
      (HierStep.currentState (moduleStructure signalType latency) hierStep))
    (satisfies : (moduleStructure signalType latency).IsSolution hierStep) :
    ∃ nextState,
      DelayLine.Step latency (inputValue signalType hierStep.inputs)
        currentState (hierStep.outputs .output) nextState ∧
      stateCorresponds signalType latency nextState
        (HierStep.nextState (moduleStructure signalType latency) hierStep) := by
  classical
  let registerCertification := Register.certification signalType
  have registerTransition (index : Fin latency) :
      ∃ nextContractState,
        (Register.cycleContract signalType).Allows {
          inputs := (hierStep.children (.delay (physicalStage index))).inputs
          currentState := fun | .stored => currentState index
          outputs := (hierStep.children (.delay (physicalStage index))).outputs
          nextState := nextContractState } ∧
        registerCertification.stateCorresponds nextContractState
          (HierStep.nextState (Register.moduleStructure signalType)
            (hierStep.children (.delay (physicalStage index)))) := by
    have realizes := ModuleStructure.child_realizes satisfies
      (.delay (physicalStage index))
    exact registerCertification.allows_of_realizes
      (fun | .stored => currentState index)
      (hierStep.children (.delay (physicalStage index))).step
      (corresponds index) realizes
  let nextContractState := fun index =>
    Classical.choose (registerTransition index)
  have allowed (index : Fin latency) :=
    (Classical.choose_spec (registerTransition index)).1
  have nextCorresponds (index : Fin latency) :=
    (Classical.choose_spec (registerTransition index)).2
  let nextState : Fin latency → Value signalType :=
    fun index => nextContractState index .stored
  have registerOutput (index : Fin latency) :
      (hierStep.children (.delay (physicalStage index))).outputs .output =
        currentState index := by
    have equation := Register.output_of_allowed (allowed index)
    change (hierStep.children (.delay (physicalStage index))).outputs .output =
      currentState index at equation
    exact equation
  have registerNext (index : Fin latency) :
      nextState index =
        (hierStep.children (.delay (physicalStage index))).inputs .input := by
    have equation := Register.next_stored_of_allowed (allowed index)
    change nextContractState index .stored =
      (hierStep.children (.delay (physicalStage index))).inputs .input at equation
    exact equation
  have boundaryOutput := boundaryOutput_of_solution signalType latency satisfies
  refine ⟨nextState, ?_, fun index => ?_⟩
  · constructor
    · by_cases positive : 0 < latency
      · have outputStage :
            (⟨latency - 1, by omega⟩ : Fin latency) =
              physicalStage ⟨0, positive⟩ := by
          apply Fin.ext
          simp [physicalStage]
        rw [dif_neg (by omega)] at boundaryOutput
        rw [boundaryOutput, outputStage, registerOutput]
        simp [positive]
      · have zero : latency = 0 := by omega
        subst latency
        rw [dif_pos rfl] at boundaryOutput
        rw [boundaryOutput]
        rfl
    · intro index
      rw [registerNext index]
      have inputWiring := delayInput_of_solution signalType latency
        satisfies (physicalStage index)
      by_cases earlier : index.val + 1 < latency
      · have stageNotFirst : (physicalStage index).val ≠ 0 := by
          simp [physicalStage]
          omega
        rw [dif_neg stageNotFirst] at inputWiring
        have previousStage :
            (⟨(physicalStage index).val - 1, by omega⟩ : Fin latency) =
              physicalStage ⟨index.val + 1, earlier⟩ := by
          apply Fin.ext
          simp [physicalStage]
          omega
        rw [inputWiring, previousStage, registerOutput]
        simp [earlier]
      · have stageFirst : (physicalStage index).val = 0 := by
          simp [physicalStage]
          omega
        rw [dif_pos stageFirst] at inputWiring
        rw [inputWiring]
        simp [inputValue, earlier]
  · change (Register.certification signalType).stateCorresponds
      (fun | .stored => nextState index)
      (HierStep.nextState (Register.moduleStructure signalType)
        (hierStep.children (.delay (physicalStage index))))
    simpa only [nextState] using nextCorresponds index

private theorem delayTrace_of_execution (signalType : SignalType)
    (latency : Nat)
    {initialStructuralState finalStructuralState :
      (moduleStructure signalType latency).State}
    {inputs : List (ShiftRegister.ports signalType).inputs.Values}
    {outputs : List (ShiftRegister.ports signalType).outputs.Values}
    (execution : (moduleStructure signalType latency).Executes
      initialStructuralState inputs outputs finalStructuralState)
    (initialDelayState : Fin latency → Value signalType)
    (corresponds : stateCorresponds signalType latency
      initialDelayState initialStructuralState) :
    ∃ finalDelayState,
      Trace (DelayLine.Step latency) initialDelayState
        (inputs.map (inputValue signalType))
        (outputs.map fun output => output .output) finalDelayState := by
  induction execution generalizing initialDelayState with
  | nil => exact ⟨initialDelayState, .nil initialDelayState⟩
  | @cons currentStructuralState nextStructuralState finalStructuralState
      remainingInputs remainingOutputs input output transition rest induction =>
      change (moduleStructure signalType latency).Realizes {
        inputs := input
        currentState := currentStructuralState
        outputs := output
        nextState := nextStructuralState } at transition
      rcases transition with ⟨hierStep, satisfies, rootEqual⟩
      have inputEqual : hierStep.inputs = input :=
        congrArg CycleStep.inputs rootEqual
      have outputEqual : hierStep.outputs = output :=
        congrArg CycleStep.outputs rootEqual
      have currentStateEqual :
          HierStep.currentState (moduleStructure signalType latency) hierStep =
            currentStructuralState :=
        congrArg CycleStep.currentState rootEqual
      have nextStateEqual :
          HierStep.nextState (moduleStructure signalType latency) hierStep =
            nextStructuralState :=
        congrArg CycleStep.nextState rootEqual
      have hierarchyCorresponds : stateCorresponds signalType latency
          initialDelayState
          (HierStep.currentState (moduleStructure signalType latency) hierStep) := by
        rw [currentStateEqual]
        exact corresponds
      obtain ⟨nextDelayState, delayStep, nextCorresponds⟩ :=
        delayStep_of_solution signalType latency initialDelayState
          hierarchyCorresponds satisfies
      rw [inputEqual, outputEqual] at delayStep
      have restCorresponds : stateCorresponds signalType latency
          nextDelayState nextStructuralState := by
        rw [← nextStateEqual]
        exact nextCorresponds
      obtain ⟨finalDelayState, laterTrace⟩ :=
        induction nextDelayState restCorresponds
      exact ⟨finalDelayState,
        .cons (inputValue signalType input) (output .output)
          delayStep laterTrace⟩

theorem optionalContract_of_execution (signalType : SignalType) (latency : Nat)
    {initialState finalState : (moduleStructure signalType latency).State}
    {inputs : List (ShiftRegister.ports signalType).inputs.Values}
    {outputs : List (ShiftRegister.ports signalType).outputs.Values}
    (execution : (moduleStructure signalType latency).Executes
      initialState inputs outputs finalState) :
    OptionalShiftRegister.contract signalType latency
      execution.toBoundaryTrace := by
  obtain ⟨initialDelayState, corresponds⟩ :=
    stateCoverage signalType latency initialState
  obtain ⟨finalDelayState, delayTrace⟩ :=
    delayTrace_of_execution signalType latency execution
      initialDelayState corresponds
  unfold OptionalShiftRegister.contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have delayed := DelayLine.input_reaches_output delayTrace t
      (by simpa using inputInTrace) (by simpa using outputInTrace)
    simpa [inputValue] using delayed

end Internal

end Silean.Modules.ShiftRegisterImplementation

namespace Silean.Modules.ShiftRegister

open Silean

theorem certification (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency) :
    ModuleStructuralRuleCertification
      (moduleStructure signalType latency positive)
      (rules signalType latency positive) :=
  ShiftRegisterImplementation.Internal.shiftRuleCertification
    signalType latency positive

noncomputable def certified (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency) :
    ModuleStructuralCertifiedStructure (rules signalType latency positive) where
  moduleStructure := moduleStructure signalType latency positive
  certification := certification signalType latency positive

end Silean.Modules.ShiftRegister

namespace Silean.Modules.OptionalShiftRegister

open Silean

theorem certification (signalType : SignalType) (latency : Nat) :
    ModuleStructuralRuleCertification (moduleStructure signalType latency)
      (rules signalType latency) :=
  ShiftRegisterImplementation.Internal.optionalRuleCertification
    signalType latency

noncomputable def certified (signalType : SignalType) (latency : Nat) :
    ModuleStructuralCertifiedStructure (rules signalType latency) where
  moduleStructure := moduleStructure signalType latency
  certification := certification signalType latency

end Silean.Modules.OptionalShiftRegister
