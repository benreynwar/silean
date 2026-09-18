import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Equality.Equality

/-! # Equality verification

This file contains the schedules and recursive certification machinery for the
hardware family defined in `Equality.lean`. Downstream modules should import
`EqualityTheorems.lean` rather than depending on these proof details. -/

namespace Silean.Modules.Equality

open Silean
open Contracts.Cycle.Certification.Layer
open Internal

@[reducible] private def bitChildContracts : Contracts.Cycle.ChildCycleContracts bitBody
  | .gate => Primitives.eqCycleContract

@[reducible] private noncomputable def bitCertifiedChildren :
    (child : bitInstances.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child)
  | .gate => ⟨.primitive Primitives.eq, Primitives.eqCertified.certification⟩

private abbrev bitOccurrence : Contracts.Cycle.Certification.Layer.RuleOccurrence
    bitBody bitChildContracts :=
  ⟨.gate, Primitives.EqRule.apply⟩

private def bitScheduleOrders : ScheduleDerivation.RuleScheduleOrders
    bitBody bitChildContracts (cycleContract .bit) where
  output | .apply => [bitOccurrence]
  state := []

private def bitDerivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    bitBody bitChildContracts (cycleContract .bit) := by
  derive_rule_schedules bitScheduleOrders

private abbrev bitRuleSchedules := bitDerivedRuleSchedules.schedules

private theorem bitCoversChildren : bitRuleSchedules.CoversChildren :=
  bitDerivedRuleSchedules.coversChildren

private def bitGateInputs (inputs : (ports .bit).inputs.Values) :
    Primitives.eq.ports.inputs.Values
  | .left => inputs .left
  | .right => inputs .right

section BitLayerCertification

variable (layerChildren : (child : bitInstances.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child))

private abbrev bitCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure bitBody layerChildren

private def bitStateCorresponds (_ : emptySignalMap.Values)
    (_ : (bitCertificationStructure layerChildren).State) : Prop := True

private theorem bitImplements : Contracts.Cycle.ImplementsSolutions
    (bitCertificationStructure layerChildren) (cycleContract .bit)
    (bitStateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for bitBody from
    layerChildren, hierStep, satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .result =
      SignalType.bit.equal (hierStep.inputs .left) (hierStep.inputs .right)
    have boundary := satisfies.1
    have gateInputs : bitBody.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .gate = bitGateInputs hierStep.inputs := by
      funext port
      cases port <;> rfl
    have gateEquation := (childMatch .gate).ruleHolds Primitives.EqRule.apply
    change (Primitives.eqOutputRule).Holds _ _ _ at gateEquation
    rw [Primitives.eqOutputRule_holds_iff] at gateEquation
    rw [gateInputs] at gateEquation
    exact (boundary .result).trans (gateEquation.trans (by
      simp [SignalType.equal, bitGateInputs]))
  · rfl

end BitLayerCertification

private noncomputable opaque bitCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer bitBody bitChildContracts
      (cycleContract .bit) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    bitRuleSchedules bitCoversChildren bitStateCorresponds
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) bitImplements

private noncomputable def bitCertifiedStructure :
    Contracts.Cycle.ModuleCycleCertifiedStructure (cycleContract .bit) :=
  bitCertifiedLayer.instantiate bitCertifiedChildren

@[simp] private theorem bitCertifiedStructure_moduleStructure :
    bitCertifiedStructure.moduleStructure = bitModuleStructure := by
  unfold bitCertifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    bitModuleStructure
  change ModuleStructure.composite bitBody (fun child =>
    (bitCertifiedChildren child).moduleStructure) =
      ModuleStructure.composite bitBody bitStructuralChildren
  congr


private theorem all_components_equal_iff (splitter : Composition.SignalSplitter)
    (left right : splitter.aggregateType.Denote) :
    (∀ component,
      splitter.outputValues (splitter.inputValues left) component =
        splitter.outputValues (splitter.inputValues right) component) ↔
      left = right := by
  constructor
  · intro pointwise
    have outputsEqual :
        splitter.outputValues (splitter.inputValues left) =
          splitter.outputValues (splitter.inputValues right) := by
      funext component
      exact pointwise component
    have combined := congrArg splitter.combineComponents outputsEqual
    simpa [splitter.combine_split] using combined
  · intro equal
    subst right
    intro component
    rfl

private abbrev Implementation (signalType : SignalType) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

/-- Recursive equality and every module below it have concrete structure. -/
def Implementation.certified {signalType : SignalType}
    (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

@[reducible] def aggregateChildContracts (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ChildCycleContracts (aggregateBody splitter)
  | .inl _ => splitter.cycleContract
  | .inr (.inl component) =>
      cycleContract (splitter.ports.outputs.signalType component)
  | .inr (.inr _) => All.cycleContract (componentCount splitter)

private def splitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) (which : Input) :
    splitter.ports.inputs.Values := match which with
  | .left => splitter.inputValues (inputs .left)
  | .right => splitter.inputValues (inputs .right)

private abbrev leftSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨splitInstance .left, Composition.SignalComponentRule.apply⟩

private abbrev rightSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨splitInstance .right, Composition.SignalComponentRule.apply⟩

private abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨componentInstance component, Rule.apply⟩

private abbrev allOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨allInstance, All.Rule.apply⟩

private def aggregateScheduleOrders (splitter : Composition.SignalSplitter) :
    ScheduleDerivation.RuleScheduleOrders (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) where
  output := fun
    | .apply => [leftSplitOccurrence splitter, rightSplitOccurrence splitter] ++
        splitter.ports.outputs.labels.values.map (componentOccurrence splitter) ++
        [allOccurrence splitter]
  state := []

private noncomputable def aggregateDerivedRuleSchedules
    (splitter : Composition.SignalSplitter) :
    ScheduleDerivation.DerivedRuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) := by
  derive_rule_schedules (aggregateScheduleOrders splitter)

private noncomputable abbrev aggregateRuleSchedules
    (splitter : Composition.SignalSplitter) :=
  (aggregateDerivedRuleSchedules splitter).schedules

private theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren :=
  (aggregateDerivedRuleSchedules splitter).coversChildren

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (layerChildren : (child : AggregateInstance splitter) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (aggregateChildContracts splitter child))

private abbrev aggregateCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (aggregateBody splitter) layerChildren

private def aggregateStateCorresponds (_ : emptySignalMap.Values)
    (_ : (aggregateCertificationStructure splitter layerChildren).State) : Prop := True

private theorem aggregateImplements :
    Contracts.Cycle.ImplementsSolutions
      (aggregateCertificationStructure splitter layerChildren)
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childStates (child : AggregateInstance splitter) :
      (aggregateChildContracts splitter child).state.Values := by
    rcases child with which | componentOrAll
    · cases which <;> exact SignalMap.emptyValues
    · rcases componentOrAll with component | allTag
      · exact SignalMap.emptyValues
      · cases allTag; exact SignalMap.emptyValues
  have childStateSubsingleton (child : AggregateInstance splitter) :
      Subsingleton (aggregateChildContracts splitter child).state.Values := by
    rcases child with which | componentOrAll
    · cases which <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    · rcases componentOrAll with component | allTag
      · change Subsingleton emptySignalMap.Values; infer_instance
      · cases allTag; change Subsingleton emptySignalMap.Values; infer_instance
  have childMatch := childSolutionsMatchContracts_of_subsingletonState
    (body := aggregateBody splitter) layerChildren hierStep satisfies
      childStates childStateSubsingleton
  have boundary := satisfies.1
  have leftSplitOutputs : (hierStep.children (splitInstance .left)).outputs =
      splitter.outputValues (splitterInputs splitter hierStep.inputs .left) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (splitInstance .left)).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (aggregateBody splitter).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs (splitInstance .left) =
          splitterInputs splitter hierStep.inputs .left := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have rightSplitOutputs : (hierStep.children (splitInstance .right)).outputs =
      splitter.outputValues (splitterInputs splitter hierStep.inputs .right) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (splitInstance .right)).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (aggregateBody splitter).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs (splitInstance .right) =
          splitterInputs splitter hierStep.inputs .right := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have componentOutputs : ∀ component,
      (hierStep.children (componentInstance component)).outputs .result =
        (splitter.ports.outputs.signalType component).equal
          (splitter.outputValues
            (splitterInputs splitter hierStep.inputs .left) component)
          (splitter.outputValues
            (splitterInputs splitter hierStep.inputs .right) component) := by
    intro component
    have equation := (childMatch (componentInstance component)).ruleHolds Rule.apply
    change (outputRule (splitter.ports.outputs.signalType component)).Holds _ _ _ at equation
    rw [outputRule_holds_iff] at equation
    have leftInput :
        ((aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs
          (componentInstance component)) .left =
        splitter.outputValues
          (splitterInputs splitter hierStep.inputs .left) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        ((aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs
          (componentInstance component)) .right =
        splitter.outputValues
          (splitterInputs splitter hierStep.inputs .right) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact equation.trans (by rw [leftInput, rightInput])
  have allHolds := (childMatch allInstance).ruleHolds All.Rule.apply
  change (All.outputRule (componentCount splitter)).Holds
    ((aggregateBody splitter).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs allInstance)
    SignalMap.emptyValues (hierStep.children allInstance).outputs at allHolds
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .result = splitter.aggregateType.equal
      (hierStep.inputs .left) (hierStep.inputs .right)
    apply Bool.eq_iff_iff.mpr
    rw [show hierStep.outputs .result =
        (hierStep.children allInstance).outputs .output by
      exact boundary .result]
    have allCharacterization := All.output_eq_true_iff_of_holds
      (componentCount splitter)
      ((aggregateBody splitter).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs allInstance)
      SignalMap.emptyValues (hierStep.children allInstance).outputs allHolds
    refine allCharacterization.trans ?_
    rw [splitter.aggregateType.equal_eq_true_iff]
    rw [← all_components_equal_iff splitter]
    constructor
    · intro every component
      have result := every (splitter.ports.outputs.labels.ordinal component)
      rw [show (aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs allInstance
            (All.input (componentCount splitter)
            (splitter.ports.outputs.labels.ordinal component)) =
          (hierStep.children (componentInstance component)).outputs .result by
        simp [HierStep.childOutputs, Wiring.childInputValues,
          aggregateBody, aggregateWiring,
          EndpointContext.instanceOutput, SignalSource.value]
        rw [All.inputIndex_input, componentAt_ordinal]] at result
      rw [componentOutputs component] at result
      exact ((splitter.ports.outputs.signalType component).equal_eq_true_iff _ _).mp result
    · intro every index
      let component := componentAt splitter index
      rw [show (aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs allInstance
            (All.input (componentCount splitter) index) =
          (hierStep.children (componentInstance component)).outputs .result by
        simp [HierStep.childOutputs, Wiring.childInputValues,
          aggregateBody, aggregateWiring,
          EndpointContext.instanceOutput, SignalSource.value]
        rw [All.inputIndex_input]]
      rw [componentOutputs component]
      apply (splitter.ports.outputs.signalType component).equal_eq_true_iff _ _ |>.mpr
      exact every component
  · rfl

end AggregateLayerCertification

private noncomputable opaque aggregateCertifiedLayer (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (aggregateRuleSchedules splitter) (aggregateCoversChildren splitter)
    (aggregateStateCorresponds splitter)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (aggregateImplements splitter)

@[reducible] noncomputable def aggregateCertifiedChildren
    (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (child : AggregateInstance splitter) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter child)
  | .inl _ => ⟨.splitter splitter, splitter.certified.certification⟩
  | .inr (.inl component) =>
      ⟨moduleStructure (splitter.ports.outputs.signalType component),
        components component⟩
  | .inr (.inr _) =>
      ⟨All.moduleStructure (componentCount splitter),
        (All.certified (componentCount splitter)).certification⟩

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
      (fun child =>
        (aggregateCertifiedChildren splitter components child).moduleStructure) =
          moduleStructure splitter.aggregateType
    cases splitter with
    | vector length element =>
        rw [moduleStructure]
        congr
        funext child
        rcases child with which | componentOrAll
        · cases which <;> rfl
        · rcases componentOrAll with component | allTag
          · rfl
          · cases allTag; rfl
    | tuple fields =>
        rw [moduleStructure]
        congr
        funext child
        rcases child with which | componentOrAll
        · cases which <;> rfl
        · rcases componentOrAll with component | allTag
          · rfl
          · cases allTag; rfl
  exact instantiated.certification.transportStructure sameStructure

private noncomputable def implementationDefinition :
    (signalType : SignalType) → Implementation signalType
  | .bit => bitCertifiedStructure.certification.transportStructure
      (bitCertifiedStructure_moduleStructure.trans (by rw [moduleStructure]))
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

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  implementation signalType

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType).bundle


end Silean.Modules.Equality
