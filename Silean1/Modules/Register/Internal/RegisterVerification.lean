import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Register.Internal.RegisterStructure

/-! Recursive certification machinery for the generic register family. -/

namespace Silean.Modules.Register

open Silean
open Contracts.Cycle.Certification.Layer

namespace Internal

@[reducible] private def aggregateBody
    (splitter : Composition.SignalSplitter) :=
  interface.aggregateBody splitter

private theorem bit_contract :
    cycleContract .bit = Primitives.registerCycleContract := rfl

private abbrev Implementation (signalType : SignalType) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
    (cycleContract signalType)

@[reducible] private def componentContracts (splitter : Composition.SignalSplitter) :
    (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (ports (splitter.ports.outputs.signalType component)) :=
  fun component => cycleContract (splitter.ports.outputs.signalType component)

@[reducible] private def aggregateChildContracts (splitter : Composition.SignalSplitter) :=
  interface.aggregateChildContracts splitter (componentContracts splitter)

private def bitImplementation : Implementation .bit := by
  have structureEq : Primitives.registerCertified.moduleStructure =
      moduleStructure .bit := by
    change Primitives.registerCertified.moduleStructure =
      moduleStructure .bit
    unfold moduleStructure
    rw [Composition.LeafwiseInterface.moduleStructure.eq_1]
    simp [Primitives.registerCertified]
  have contractEq : Primitives.registerCertified.cycleContract =
      cycleContract .bit := by
    rw [show Primitives.registerCertified.cycleContract =
      Primitives.registerCycleContract by
        simp [Primitives.registerCertified]]
    exact bit_contract.symm
  exact Primitives.registerCertified.certification
    |>.transportStructure structureEq
    |>.transportContract contractEq

private def aggregateSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values :=
  splitter.inputValues (inputs .input)

private abbrev splitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.splitterOccurrence splitter
    (componentContracts splitter) .unit

private abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.componentOccurrence splitter
    (componentContracts splitter) component
      Primitives.RegisterRule.observe

private abbrev combineOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.combinerOccurrence splitter
    (componentContracts splitter) .output

private def aggregateScheduleOrders (splitter : Composition.SignalSplitter) :
    ScheduleDerivation.RuleScheduleOrders (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) where
  output := fun
    | .observe => splitter.ports.outputs.labels.values.map
        (componentOccurrence splitter) ++ [combineOccurrence splitter]
  state := [splitOccurrence splitter]

private noncomputable def aggregateDerivedRuleSchedules
    (splitter : Composition.SignalSplitter) :
    ScheduleDerivation.DerivedRuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) := by
  cases splitter with
  | vector length element =>
      derive_rule_schedules (aggregateScheduleOrders (.vector length element))
  | tuple fields =>
      derive_rule_schedules (aggregateScheduleOrders (.tuple fields))

private noncomputable abbrev aggregateRuleSchedules
    (splitter : Composition.SignalSplitter) :=
  (aggregateDerivedRuleSchedules splitter).schedules

private theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren :=
  (aggregateDerivedRuleSchedules splitter).coversChildren

@[reducible] private def aggregateComponentContractState (splitter : Composition.SignalSplitter)
    (contractState : (stateMap splitter.aggregateType).Values)
    (component : splitter.ports.outputs.Label) :
    (stateMap (splitter.ports.outputs.signalType component)).Values := fun
  | .stored => splitter.outputValues
      (splitter.inputValues (contractState .stored)) component

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (layerChildren : (child : (aggregateBody splitter).instancePorts.Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (aggregateChildContracts splitter child))

private abbrev aggregateCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (aggregateBody splitter) layerChildren

private def aggregateStateCorresponds
    (contractState : (stateMap splitter.aggregateType).Values)
    (structuralState :
      (aggregateCertificationStructure splitter layerChildren).State) : Prop :=
  ∀ component,
    (layerChildren
      (.component component)).certification.stateCorresponds
      (aggregateComponentContractState splitter contractState component)
      (structuralState (.component component))

private theorem aggregateHasCorrespondingState
    (structuralState :
      (aggregateCertificationStructure splitter layerChildren).State) :
    ∃ contractState,
      aggregateStateCorresponds splitter layerChildren contractState structuralState := by
  let Property := fun component contractState =>
    (layerChildren
      (.component component)).certification.stateCorresponds contractState
      (structuralState (.component component))
  have available : ∀ component, ∃ contractState, Property component contractState :=
    fun component => (layerChildren
      (.component component)).certification.hasCorrespondingState
      (structuralState (.component component))
  rcases splitter.ports.outputs.labels.exists_pi Property available with
    ⟨componentStates, correspond⟩
  let componentValues : splitter.ports.outputs.Values :=
    fun component => componentStates component .stored
  let contractState : (stateMap splitter.aggregateType).Values := fun
    | .stored => splitter.combineComponents componentValues
  refine ⟨contractState, ?_⟩
  intro component
  have stateEqual : aggregateComponentContractState splitter contractState component =
      componentStates component := by
    funext statePort
    cases statePort
    change splitter.outputValues
      (splitter.inputValues (contractState .stored)) component =
        componentValues component
    exact congrFun (splitter.split_combined componentValues) component
  rw [stateEqual]
  exact correspond component

private theorem aggregateImplements :
    Contracts.Cycle.ImplementsSolutions
      (aggregateCertificationStructure splitter layerChildren)
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have componentMatch (component) :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
      (body := aggregateBody splitter) layerChildren hierStep satisfies
      (.component component)
      (aggregateComponentContractState splitter contractState component)
      (corresponds component)
  have combineOutputs : (hierStep.children (.combiner .output)).outputs =
      splitter.combiner.outputValues
        ((aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (.combiner .output)) := by
    derive_empty_state_child_match combinerMatch for (.combiner .output)
      in aggregateBody splitter from layerChildren, hierStep, satisfies
    exact (Composition.SignalCombiner.outputRule_holds_iff splitter.combiner _ _ _).mp
      (combinerMatch.ruleHolds Composition.SignalComponentRule.apply)
  have splitOutputs : (hierStep.children (.splitter .unit)).outputs =
      splitter.outputValues (aggregateSplitterInputs splitter hierStep.inputs) := by
    derive_empty_state_child_match splitterMatch for (.splitter .unit)
      in aggregateBody splitter from layerChildren, hierStep, satisfies
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      (splitterMatch.ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (aggregateBody splitter).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs (.splitter .unit) =
          aggregateSplitterInputs splitter hierStep.inputs := by
      cases splitter <;> funext port <;> cases port <;> rfl
    change (hierStep.children (.splitter .unit)).outputs =
      splitter.outputValues
        ((aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (.splitter .unit)) at holds
    rw [inputsEqual] at holds
    exact holds
  let nextContractState : (stateMap splitter.aggregateType).Values := fun
    | .stored => hierStep.inputs .input
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      change hierStep.outputs .output = contractState .stored
      have componentOutputs : ∀ component,
          (hierStep.children (.component component)).outputs .output =
            aggregateComponentContractState splitter contractState component .stored := by
        intro component
        have evaluated := (componentMatch component).ruleHolds
          Primitives.RegisterRule.observe
        exact (outputRule_holds_iff _ _ _ _).mp evaluated
      have boundaryOutput := boundary Primitives.SingleOutput.output
      cases splitter with
      | vector length element =>
          funext index
          have componentOutput := componentOutputs index
          simpa [Wiring.childInputValues, aggregateBody,
            Composition.LeafwiseInterface.aggregateWiring,
            Composition.LeafwiseInterface.aggregateContext,
            Composition.LeafwiseInterface.aggregateInstances, aggregateComponentContractState,
            Composition.SignalSplitter.outputValues, Composition.SignalSplitter.inputValues,
            Composition.SignalCombiner.outputValues, SignalSource.value] using
            congrFun (boundaryOutput.trans
              (congrFun combineOutputs Composition.AggregatePort.value)) index |>.trans
                componentOutput
      | tuple fields =>
          change (hierStep.children (.combiner .output)).outputs =
            Composition.SignalCombiner.outputValues (.tuple fields)
              ((aggregateBody (.tuple fields)).wiring.childInputValues
                hierStep.inputs hierStep.childOutputs
                (.combiner .output)) at combineOutputs
          have combineInputs :
              (aggregateBody (.tuple fields)).wiring.childInputValues
                hierStep.inputs hierStep.childOutputs (.combiner .output) =
              (fun component =>
                (hierStep.children (.component component)).outputs .output) := by
            funext component
            rfl
          rw [combineInputs] at combineOutputs
          have boundaryOutput' : hierStep.outputs .output =
              (hierStep.children (.combiner .output)).outputs
                Composition.AggregatePort.value := by
            change hierStep.outputs .output =
              (hierStep.children (.combiner .output)).outputs
                Composition.AggregatePort.value at boundaryOutput
            exact boundaryOutput
          have combinedOutput :=
            congrFun combineOutputs Composition.AggregatePort.value
          change (hierStep.children (.combiner .output)).outputs
              Composition.AggregatePort.value =
            fields.assemble (fun component =>
              (hierStep.children (.component component)).outputs .output) at combinedOutput
          rw [boundaryOutput', combinedOutput]
          change fields.assemble (fun component =>
            (hierStep.children (.component component)).outputs .output) =
              contractState .stored
          have componentFunction : (fun component : fields.Position =>
              (hierStep.children (.component component)).outputs .output) =
              fields.get (contractState .stored) := by
            funext component
            exact componentOutputs component
          rw [componentFunction]
          exact fields.assemble_get (contractState .stored)
    · rfl
  · intro component
    have nextCorresponds := (componentMatch component).nextCorresponds
    change (layerChildren
      (.component component)).certification.stateCorresponds
      (aggregateComponentContractState splitter nextContractState component)
      (HierStep.nextState (layerChildren (.component component)).moduleStructure
        (hierStep.children (.component component)))
    rw [show aggregateComponentContractState splitter nextContractState component =
        (cycleContract (splitter.ports.outputs.signalType component)).stateRule.apply
          ((aggregateBody splitter).wiring.childInputValues
            hierStep.inputs hierStep.childOutputs (.component component))
          (aggregateComponentContractState splitter contractState component) by
      funext statePort
      cases statePort
      have childInputValue :
          ((aggregateBody splitter).wiring.childInputValues
            hierStep.inputs hierStep.childOutputs
              (.component component)) .input =
          splitter.outputValues
            (splitter.inputValues (hierStep.inputs .input)) component := by
        cases splitter <;> exact congrFun splitOutputs component
      simpa [stateRule, Contracts.Cycle.CycleStateRule.apply] using
        childInputValue.symm]
    exact nextCorresponds

end AggregateLayerCertification

private noncomputable opaque aggregateCertifiedLayer (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (aggregateRuleSchedules splitter) (aggregateCoversChildren splitter)
    (aggregateStateCorresponds splitter) (aggregateHasCorrespondingState splitter)
    (aggregateImplements splitter)

@[reducible] private noncomputable def aggregateCertifiedChildren
    (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (child : (aggregateBody splitter).instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter child)
  | .splitter _ => ⟨.splitter splitter, splitter.certified.certification⟩
  | .component component =>
      ⟨moduleStructure (splitter.ports.outputs.signalType component),
        components component⟩
  | .combiner _ =>
      ⟨.combiner splitter.combiner, splitter.combiner.certified.certification⟩

private noncomputable def aggregateImplementation (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implementation splitter.aggregateType := by
  let instantiated := (aggregateCertifiedLayer splitter).instantiate
    (aggregateCertifiedChildren splitter components)
  have sameStructure : instantiated.moduleStructure =
      moduleStructure splitter.aggregateType := by
    unfold instantiated Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    change ModuleStructure.composite (aggregateBody splitter)
      (fun child => (aggregateCertifiedChildren splitter components child).moduleStructure) =
        moduleStructure splitter.aggregateType
    unfold moduleStructure
    cases splitter with
    | vector length element =>
        rw [Composition.LeafwiseInterface.moduleStructure.eq_2]
        congr
        funext child
        cases child <;> rfl
    | tuple fields =>
        rw [Composition.LeafwiseInterface.moduleStructure.eq_3]
        congr
        funext child
        cases child <;> rfl
  exact instantiated.certification.transportStructure sameStructure

private noncomputable def implementationDefinition :
    (signalType : SignalType) → Implementation signalType
  | .bit => bitImplementation
  | .vector length elementType =>
      aggregateImplementation (.vector length elementType) fun _ =>
        implementationDefinition elementType
  | .tuple fields =>
      aggregateImplementation (.tuple fields) fun component =>
        implementationDefinition (fields.typeAt component)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

private noncomputable opaque implementation (signalType : SignalType) :
    Implementation signalType := implementationDefinition signalType

end Internal

noncomputable def certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  Internal.implementation signalType

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType).bundle

end Silean.Modules.Register
