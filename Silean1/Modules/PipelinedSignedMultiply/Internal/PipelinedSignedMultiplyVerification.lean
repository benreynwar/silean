import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.PipelinedSignedMultiply.Internal.PipelinedSignedMultiplyStructure
import Silean.Semantics.DelayLine
import Silean.Semantics.StructuralExecution

/-! Structural certification and trace correctness for the provisional
output-registered signed multiplier. -/

namespace Silean.Modules.PipelinedSignedMultiply

open Silean
open Silean.Authoring

open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (leftWidth : Nat) (rightWidth : Nat)
    (latency : Nat) for body leftWidth rightWidth latency where
  product := SignedMultiply.certification leftWidth rightWidth,
  delay (_stage : Fin latency) :=
    Register.certification (.vector (leftWidth + rightWidth) .bit)

@[reducible] private def childRules (leftWidth rightWidth latency : Nat) :
    ModuleStructuralCertification.Layer.ChildRules
      (body leftWidth rightWidth latency) :=
  Contracts.Cycle.Certification.Layer.childStructuralRules
    (body leftWidth rightWidth latency)
    (childContracts leftWidth rightWidth latency)

private abbrev productOccurrence (leftWidth rightWidth latency : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth latency)
      (childRules leftWidth rightWidth latency) :=
  ⟨.product, SignedMultiply.Rule.apply⟩

private abbrev delayOccurrence (leftWidth rightWidth latency : Nat)
    (stage : Fin latency) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth latency)
      (childRules leftWidth rightWidth latency) :=
  ⟨.delay stage, Primitives.RegisterRule.observe⟩

module_complete_schedule completeSchedule (leftWidth : Nat) (rightWidth : Nat)
    (latency : Nat)
    for body leftWidth rightWidth latency
    with childRules leftWidth rightWidth latency := from (
      [productOccurrence leftWidth rightWidth latency] ++
      (Enumeration.fin latency).values.map
        (delayOccurrence leftWidth rightWidth latency))

/-- Contract-independent existence and uniqueness of the flat multiplier and
register hierarchy. -/
theorem Internal.structuralCertification (leftWidth rightWidth latency : Nat) :
    ModuleStructuralCertification
    (moduleStructure leftWidth rightWidth latency) :=
  (completeSchedule leftWidth rightWidth latency).certifyComposite
    (structuralChildren leftWidth rightWidth latency)
    (Contracts.Cycle.Certification.Layer.structuralChildren
      (certifiedChildren leftWidth rightWidth latency))
    (certifiedChildren_moduleStructure leftWidth rightWidth latency)

namespace Internal

private abbrev Value (leftWidth rightWidth : Nat) :=
  Fin (leftWidth + rightWidth) → Bool

/-- Convert the delay-line's output-first indexing to physical register order,
where register zero is nearest the multiplier. -/
private def physicalStage {latency : Nat} (index : Fin latency) : Fin latency :=
  ⟨latency - 1 - index.val, by omega⟩

private def stateCorresponds (leftWidth rightWidth latency : Nat)
    (state : Fin latency → Value leftWidth rightWidth)
    (structuralState : (moduleStructure leftWidth rightWidth latency).State) : Prop :=
  ∀ index,
    (Register.certification (.vector (leftWidth + rightWidth) .bit)).stateCorresponds
      (fun | .stored => state index)
      (structuralState (.delay (physicalStage index)))

private theorem stateCoverage (leftWidth rightWidth latency : Nat)
    (structuralState : (moduleStructure leftWidth rightWidth latency).State) :
    ∃ state, stateCorresponds leftWidth rightWidth latency state structuralState := by
  classical
  let contractState : (index : Fin latency) →
      (Register.cycleContract
        (.vector (leftWidth + rightWidth) .bit)).state.Values :=
    fun index => Classical.choose
      ((Register.certification (.vector (leftWidth + rightWidth) .bit))
        |>.hasCorrespondingState
          (structuralState (.delay (physicalStage index))))
  let state : Fin latency → Value leftWidth rightWidth :=
    fun index => contractState index .stored
  refine ⟨state, fun index => ?_⟩
  have corresponds := Classical.choose_spec
    ((Register.certification (.vector (leftWidth + rightWidth) .bit))
      |>.hasCorrespondingState
        (structuralState (.delay (physicalStage index))))
  simpa only [state, contractState] using corresponds

private def inputProduct (leftWidth rightWidth : Nat)
    (inputs : (ports leftWidth rightWidth).inputs.Values) :
    Value leftWidth rightWidth :=
  SignedMultiply.resultValue leftWidth rightWidth
    (inputs .left) (inputs .right)

private theorem productOutput_of_solution (leftWidth rightWidth latency : Nat)
    {hierStep : HierStep (moduleStructure leftWidth rightWidth latency)}
    (satisfies : (moduleStructure leftWidth rightWidth latency).IsSolution
      hierStep) :
    (hierStep.children .product).outputs .result =
      inputProduct leftWidth rightWidth hierStep.inputs := by
  have realizes := ModuleStructure.child_realizes satisfies (.product)
  obtain ⟨_, _, allowed⟩ :=
    SignedMultiply.allowed_of_realization leftWidth rightWidth realizes
  have result :=
    SignedMultiply.cycleContract.result leftWidth rightWidth allowed
  have leftInput := ModuleStructure.child_input satisfies (.product) (.left)
  have rightInput := ModuleStructure.child_input satisfies (.product) (.right)
  change (hierStep.children .product).inputs .left =
    hierStep.inputs .left at leftInput
  change (hierStep.children .product).inputs .right =
    hierStep.inputs .right at rightInput
  change (hierStep.children .product).outputs .result =
    SignedMultiply.resultValue leftWidth rightWidth
      ((hierStep.children .product).inputs .left)
      ((hierStep.children .product).inputs .right) at result
  simpa only [inputProduct, leftInput, rightInput] using result

private theorem delayInput_of_solution (leftWidth rightWidth latency : Nat)
    {hierStep : HierStep (moduleStructure leftWidth rightWidth latency)}
    (satisfies : (moduleStructure leftWidth rightWidth latency).IsSolution
      hierStep) (stage : Fin latency) :
    (hierStep.children (.delay stage)).inputs .input =
      if _first : stage.val = 0 then
        (hierStep.children .product).outputs .result
      else
        (hierStep.children (.delay ⟨stage.val - 1, by omega⟩)).outputs
          .output := by
  have equation :=
    ModuleStructure.child_input satisfies (.delay stage) (.input)
  by_cases first : stage.val = 0
  · simpa [wiring, first, EndpointContext.instanceOutput, SignalSource.value]
      using equation
  · simpa [wiring, first, EndpointContext.instanceOutput, SignalSource.value]
      using equation

private theorem boundaryOutput_of_solution (leftWidth rightWidth latency : Nat)
    {hierStep : HierStep (moduleStructure leftWidth rightWidth latency)}
    (satisfies : (moduleStructure leftWidth rightWidth latency).IsSolution
      hierStep) :
    hierStep.outputs .result =
      if zero : latency = 0 then
        (hierStep.children .product).outputs .result
      else
        (hierStep.children (.delay ⟨latency - 1, by omega⟩)).outputs
          .output := by
  have equation := ModuleStructure.parent_output satisfies (.result)
  by_cases zero : latency = 0
  · simpa [wiring, zero, EndpointContext.instanceOutput, SignalSource.value]
      using equation
  · simpa [wiring, zero, EndpointContext.instanceOutput, SignalSource.value]
      using equation

private theorem delayStep_of_solution (leftWidth rightWidth latency : Nat)
    (currentState : Fin latency → Value leftWidth rightWidth)
    {hierStep : HierStep (moduleStructure leftWidth rightWidth latency)}
    (corresponds : stateCorresponds leftWidth rightWidth latency currentState
      (HierStep.currentState
        (moduleStructure leftWidth rightWidth latency) hierStep))
    (satisfies : (moduleStructure leftWidth rightWidth latency).IsSolution
      hierStep) :
    ∃ nextState,
      DelayLine.Step latency
        (inputProduct leftWidth rightWidth hierStep.inputs)
        currentState (hierStep.outputs .result) nextState ∧
      stateCorresponds leftWidth rightWidth latency nextState
        (HierStep.nextState
          (moduleStructure leftWidth rightWidth latency) hierStep) := by
  classical
  let registerCertification :=
    Register.certification (.vector (leftWidth + rightWidth) .bit)
  have registerTransition (index : Fin latency) :
      ∃ nextContractState,
        (Register.cycleContract
          (.vector (leftWidth + rightWidth) .bit)).Allows {
            inputs := (hierStep.children
              (.delay (physicalStage index))).inputs
            currentState := fun | .stored => currentState index
            outputs := (hierStep.children
              (.delay (physicalStage index))).outputs
            nextState := nextContractState } ∧
        registerCertification.stateCorresponds nextContractState
          (HierStep.nextState
            (Register.moduleStructure
              (.vector (leftWidth + rightWidth) .bit))
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
  let nextState : Fin latency → Value leftWidth rightWidth :=
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
  have productOutput := productOutput_of_solution
    leftWidth rightWidth latency satisfies
  have boundaryOutput := boundaryOutput_of_solution
    leftWidth rightWidth latency satisfies

  refine ⟨nextState, ?_, fun index => ?_⟩
  · constructor
    · by_cases positive : 0 < latency
      · have outputStage :
            (⟨latency - 1, by omega⟩ : Fin latency) = physicalStage ⟨0, positive⟩ := by
          apply Fin.ext
          simp [physicalStage]
        rw [dif_neg (by omega)] at boundaryOutput
        rw [boundaryOutput, outputStage, registerOutput]
        simp [positive]
      · have zero : latency = 0 := by omega
        subst latency
        rw [dif_pos rfl] at boundaryOutput
        rw [boundaryOutput, productOutput]
        simp
    · intro index
      rw [registerNext index]
      have inputWiring := delayInput_of_solution leftWidth rightWidth latency
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
        rw [inputWiring, productOutput]
        simp [earlier]
  · change (Register.certification
      (.vector (leftWidth + rightWidth) .bit)).stateCorresponds
        (fun | .stored => nextState index)
        (HierStep.nextState
          (Register.moduleStructure (.vector (leftWidth + rightWidth) .bit))
          (hierStep.children (.delay (physicalStage index))))
    simpa only [nextState] using nextCorresponds index

private theorem delayTrace_of_execution (leftWidth rightWidth latency : Nat)
    {initialStructuralState finalStructuralState :
      (moduleStructure leftWidth rightWidth latency).State}
    {inputs : List (ports leftWidth rightWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth).outputs.Values}
    (execution : (moduleStructure leftWidth rightWidth latency).Executes
      initialStructuralState inputs outputs finalStructuralState)
    (initialDelayState : Fin latency → Value leftWidth rightWidth)
    (corresponds : stateCorresponds leftWidth rightWidth latency
      initialDelayState initialStructuralState) :
    ∃ finalDelayState,
      Trace (DelayLine.Step latency) initialDelayState
        (inputs.map (inputProduct leftWidth rightWidth))
        (outputs.map fun output => output .result) finalDelayState := by
  induction execution generalizing initialDelayState with
  | nil =>
      exact ⟨initialDelayState, .nil initialDelayState⟩
  | @cons currentStructuralState nextStructuralState finalStructuralState
      remainingInputs remainingOutputs input output transition rest induction =>
      change (moduleStructure leftWidth rightWidth latency).Realizes {
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
          HierStep.currentState
              (moduleStructure leftWidth rightWidth latency) hierStep =
            currentStructuralState :=
        congrArg CycleStep.currentState rootEqual
      have nextStateEqual :
          HierStep.nextState
              (moduleStructure leftWidth rightWidth latency) hierStep =
            nextStructuralState :=
        congrArg CycleStep.nextState rootEqual
      have hierarchyCorresponds : stateCorresponds leftWidth rightWidth latency
          initialDelayState
          (HierStep.currentState
            (moduleStructure leftWidth rightWidth latency) hierStep) := by
        rw [currentStateEqual]
        exact corresponds
      obtain ⟨nextDelayState, delayStep, nextCorresponds⟩ :=
        delayStep_of_solution leftWidth rightWidth latency initialDelayState
          hierarchyCorresponds satisfies
      rw [inputEqual, outputEqual] at delayStep
      have restCorresponds : stateCorresponds leftWidth rightWidth latency
          nextDelayState nextStructuralState := by
        rw [← nextStateEqual]
        exact nextCorresponds
      obtain ⟨finalDelayState, laterTrace⟩ :=
        induction nextDelayState restCorresponds
      exact ⟨finalDelayState,
        .cons (inputProduct leftWidth rightWidth input)
          (output .result) delayStep laterTrace⟩

/-- Every structural execution satisfies the public all-time latency
contract. -/
theorem contract_of_execution (leftWidth rightWidth latency : Nat)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth latency).State}
    {inputs : List (ports leftWidth rightWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth).outputs.Values}
    (execution : (moduleStructure leftWidth rightWidth latency).Executes
      initialState inputs outputs finalState) :
    contract leftWidth rightWidth latency execution.toBoundaryTrace := by
  obtain ⟨initialDelayState, corresponds⟩ :=
    stateCoverage leftWidth rightWidth latency initialState
  obtain ⟨finalDelayState, delayTrace⟩ :=
    delayTrace_of_execution leftWidth rightWidth latency execution
      initialDelayState corresponds
  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have delayed := DelayLine.input_reaches_output delayTrace t
      (by simpa using inputInTrace) (by simpa using outputInTrace)
    change @Eq (Value leftWidth rightWidth)
      (outputs.get ⟨t + latency, outputInTrace⟩ .result)
      (SignedMultiply.resultValue leftWidth rightWidth
        (inputs.get ⟨t, inputInTrace⟩ .left)
        (inputs.get ⟨t, inputInTrace⟩ .right))
    simpa [inputProduct] using delayed

end Internal

end Silean.Modules.PipelinedSignedMultiply
