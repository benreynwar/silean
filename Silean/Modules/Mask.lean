import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.And
import Silean.Composition.SignalLogic

namespace Silean.Modules.Mask

open Silean

/-! Gates every bit of a value with one shared mask bit. Aggregate signal types
are handled recursively. -/

inductive Input | value | mask
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def interface : Composition.LeafwiseInterface where
  Input := Input
  inputs := inferInstance
  RecursiveInput := PUnit
  recursiveInputs := Enumeration.punit
  FixedInput := PUnit
  fixedInputs := Enumeration.punit
  inputLayout := {
    classify := fun | .value => .inl .unit | .mask => .inr .unit
    label := fun | .inl _ => .value | .inr _ => .mask
    classify_label := by
      intro part
      cases part with
      | inl recursive => cases recursive; rfl
      | inr fixed => cases fixed; rfl
    label_classify := by intro input; cases input <;> rfl }
  fixedInputType := fun | .unit => .bit
  Output := Output
  outputs := inferInstance
  State := NoSignal
  states := inferInstance

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  interface.inputMap signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  interface.outputMap signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  interface.ports signalType

inductive Rule | apply
deriving Enumeration

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons .bit .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((inputMap signalType).select .mask).prepend .value
  writesOutputs := (outputMap signalType).select .result
  target | (value, (mask, ())), _ => (signalType.mask value mask, ())

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

/-! ## Hardware structure

The bit specialization is a readable wrapper around the closed AND
primitive. -/

inductive BitInstance
  /-- The one-bit AND primitive. -/
  | gate
deriving Enumeration

@[reducible] def bitInstances : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.and.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instancePorts where
  -- The gate result is the masked bit.
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  -- Apply the shared mask to the value bit.
  instanceInput
    | .gate, .left => bitContext.moduleInput .value
    | .gate, .right => bitContext.moduleInput .mask

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildContracts : Contracts.Cycle.ChildCycleContracts bitBody
  | .gate => Primitives.andCycleContract

@[reducible] def bitStructuralChildren :
    (child : bitInstances.Name) → ModuleStructure (bitInstances.ports child)
  | .gate => .primitive Primitives.and

@[reducible] noncomputable def bitCertifiedChildren :
    (child : bitInstances.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child)
  | .gate => ⟨.primitive Primitives.and, Primitives.andCertified.certification⟩

def bitModuleStructure : ModuleStructure (ports .bit) :=
  .composite bitBody bitStructuralChildren

abbrev bitRule : Contracts.Cycle.Certification.Layer.RuleOccurrence
    bitBody bitChildContracts :=
  ⟨.gate, Primitives.AndRule.apply⟩

def bitOutputSchedule : Contracts.Cycle.Certification.Layer.OutputSchedule
    bitBody bitChildContracts
    (cycleContract .bit) .apply :=
  .call bitRule
    (by
      intro input member
      cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
          bitBody, bitWiring,
          bitContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output member
      cases output
      exact ⟨Primitives.AndRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Contracts.Cycle.Certification.Layer.StateSchedule
    bitBody bitChildContracts :=
  .done (by
    intro child input member
    cases child
    simp [bitChildContracts, Primitives.andCycleContract,
      Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

def bitRuleSchedules : Contracts.Cycle.Certification.Layer.RuleSchedules
    bitBody bitChildContracts
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  right
  cases child
  change Primitives.AndRule at rule
  cases rule
  refine ⟨.apply, ?_⟩
  change bitRule ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule,
    Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

section BitLayerCertification

variable (layerChildren : (child : bitInstances.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child))

private abbrev bitCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure bitBody layerChildren

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : (bitCertificationStructure layerChildren).State) : Prop := True

private theorem bitImplements : Contracts.Cycle.Implements
    (bitCertificationStructure layerChildren) (cycleContract .bit)
    (emptyStateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  letI : Subsingleton
      ((bitChildContracts .gate).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have gateEvaluates :=
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal
        satisfies .gate SignalMap.emptyValues).1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [show (outputRule .bit).Holds inputs contractState proposal.outputs ↔
        proposal.outputs .result = (inputs .value && inputs .mask) by
      simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
        SignalSelection.Matches, SignalSelection.project,
        SignalSelection.prepend, SignalMap.select, SignalType.mask]]
    rcases proposal with ⟨outputs, children⟩
    have boundary := satisfies.1
    change outputs .result = (inputs .value && inputs .mask)
    have boundaryResult := boundary .result
    change outputs .result = (children .gate).outputs .output at boundaryResult
    have gateOutput : (children .gate).outputs .output =
        (inputs .value && inputs .mask) := by
      exact (Primitives.andOutputRule_holds_iff _ _ _).mp
        (gateEvaluates.1 Primitives.AndRule.apply)
    exact boundaryResult.trans gateOutput
  · rfl

end BitLayerCertification

noncomputable opaque bitCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer bitBody bitChildContracts
      (cycleContract .bit) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    bitRuleSchedules bitCoversChildren emptyStateCorresponds
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) bitImplements

noncomputable def bitCertifiedStructure :
    Contracts.Cycle.ModuleCycleCertifiedStructure (cycleContract .bit) :=
  bitCertifiedLayer.instantiate bitCertifiedChildren

@[simp] theorem bitCertifiedStructure_moduleStructure :
    bitCertifiedStructure.moduleStructure = bitModuleStructure := by
  unfold bitCertifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    bitModuleStructure
  change ModuleStructure.composite bitBody (fun child =>
    (bitCertifiedChildren child).moduleStructure) =
      ModuleStructure.composite bitBody bitStructuralChildren
  congr

@[reducible] def aggregateBody (splitter : Composition.SignalSplitter) :=
  interface.aggregateBody splitter

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  := interface.moduleStructure bitModuleStructure

abbrev Implementation (signalType : SignalType) :=
  Contracts.Cycle.ModuleCycleCertification
    (moduleStructure signalType) (cycleContract signalType)

def Implementation.certified (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  implementation.bundle

theorem moduleStructure_bit : moduleStructure .bit = bitModuleStructure := by
  rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_1]

noncomputable def bitImplementation : Implementation .bit :=
  bitCertifiedStructure.certification.transportStructure
    (bitCertifiedStructure_moduleStructure.trans moduleStructure_bit.symm)

/-! ## Recursive aggregate layer -/

@[reducible] def componentContracts (splitter : Composition.SignalSplitter) :
    (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (ports (splitter.ports.outputs.signalType component)) :=
  fun component => cycleContract (splitter.ports.outputs.signalType component)

@[reducible] def aggregateChildContracts (splitter : Composition.SignalSplitter) :=
  interface.aggregateChildContracts splitter (componentContracts splitter)

abbrev splitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.splitterOccurrence splitter (componentContracts splitter) .unit

abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.componentOccurrence splitter (componentContracts splitter)
    component Rule.apply

abbrev combineOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.combinerOccurrence splitter (componentContracts splitter) .result

@[simp] theorem splitOccurrence_writes (splitter : Composition.SignalSplitter) :
    (splitOccurrence splitter).writes = splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

noncomputable def componentSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [splitOccurrence splitter] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [splitOccurrence splitter] ∨
          ∃ component, called = componentOccurrence splitter component)
      [splitOccurrence splitter] :=
  interface.callComponentsAfter splitter (componentContracts splitter)
    [splitOccurrence splitter] (fun _ => Rule.apply)
    (by
      intro component member
      simp only [List.mem_singleton] at member
      have childEqual := congrArg
        Contracts.Cycle.Certification.Layer.RuleOccurrence.child member
      cases childEqual)
    (by
      intro component input _
      cases input with
      | value =>
          cases splitter with
          | vector length element =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [splitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [splitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩
      | mask =>
          cases splitter <;>
            simp [outputRule, SignalSelection.prepend, SignalMap.select,
              SignalSelection.labels,
              Contracts.Cycle.Certification.Layer.sourceAvailable,
              aggregateBody, Composition.LeafwiseInterface.aggregateWiring,
              Composition.LeafwiseInterface.aggregateComponentInputSource,
              Composition.LeafwiseInterface.aggregateContext,
              Composition.LeafwiseInterface.aggregateInstances, interface,
              Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput])

noncomputable def aggregateAfterSplitSchedule
    (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Contracts.Cycle.Certification.Layer.BoundaryReady
        (aggregateBody splitter) (aggregateChildContracts splitter)
        (outputRule splitter.aggregateType).writesOutputs.labels
        (fun input => input ∈
          (outputRule splitter.aggregateType).readsInputs.labels))
      [splitOccurrence splitter] := by
  apply (componentSchedule splitter).append
  refine .call (combineOccurrence splitter) ?_ ?_ (.done ?_)
  · intro input _
    cases splitter with
    | vector length element =>
        exact ⟨Rule.apply,
          (componentSchedule (.vector length element)).finished.2.1 input,
          by change Output.result ∈ [Output.result]; simp⟩
    | tuple fields =>
        exact ⟨Rule.apply,
          (componentSchedule (.tuple fields)).finished.2.1 input,
          by change Output.result ∈ [Output.result]; simp⟩
  · intro present
    rcases (componentSchedule splitter).finished.2.2 _ present with
      atStart | fromComponent
    · simp only [List.mem_singleton] at atStart
      have childEqual := congrArg
        Contracts.Cycle.Certification.Layer.RuleOccurrence.child atStart
      cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      cases equal
  · intro output _
    cases output
    cases splitter <;>
      exact ⟨Composition.SignalComponentRule.apply, by simp,
        by change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]
           simp⟩

noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.OutputSchedule
      (aggregateBody splitter) (aggregateChildContracts splitter)
      (cycleContract splitter.aggregateType) .apply := by
  refine .call (splitOccurrence splitter) ?_ (by simp) ?_
  · intro input _
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
        aggregateBody, Composition.LeafwiseInterface.aggregateWiring,
        Composition.LeafwiseInterface.aggregateSplitterInputSource,
        Composition.LeafwiseInterface.aggregateContext,
        Composition.LeafwiseInterface.aggregateInstances, interface,
        Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput]
  · exact aggregateAfterSplitSchedule splitter

def aggregateStateSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  .done (by
    intro child input member
    cases child with
    | splitter recursiveInput =>
        cases recursiveInput
        simp [aggregateChildContracts,
          Composition.LeafwiseInterface.aggregateChildContracts,
          Composition.SignalSplitter.cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member
    | component component =>
        simp [aggregateChildContracts,
          Composition.LeafwiseInterface.aggregateChildContracts,
          componentContracts, cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member
    | combiner output =>
        cases output
        simp [aggregateChildContracts,
          Composition.LeafwiseInterface.aggregateChildContracts,
          Composition.SignalCombiner.cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleSchedules
      (aggregateBody splitter) (aggregateChildContracts splitter)
      (cycleContract splitter.aggregateType) where
  output | .apply => aggregateOutputSchedule splitter
  state := aggregateStateSchedule splitter

theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  cases child with
  | splitter recursiveInput =>
      cases recursiveInput
      change Composition.SignalComponentRule at rule
      cases rule
      change splitOccurrence splitter ∈
        (aggregateOutputSchedule splitter).finalAvailability
      unfold aggregateOutputSchedule
      change splitOccurrence splitter ∈
        (aggregateAfterSplitSchedule splitter).finalAvailability
      unfold aggregateAfterSplitSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem (combineOccurrence splitter)
        ((componentSchedule splitter).finished.1
          (splitOccurrence splitter) (by simp))
  | component component =>
      change Rule at rule
      cases rule
      change componentOccurrence splitter component ∈
        (aggregateOutputSchedule splitter).finalAvailability
      unfold aggregateOutputSchedule
      change componentOccurrence splitter component ∈
        (aggregateAfterSplitSchedule splitter).finalAvailability
      unfold aggregateAfterSplitSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem (combineOccurrence splitter)
        ((componentSchedule splitter).finished.2.1 component)
  | combiner output =>
      cases output
      change Composition.SignalComponentRule at rule
      cases rule
      change combineOccurrence splitter ∈
        (aggregateOutputSchedule splitter).finalAvailability
      unfold aggregateOutputSchedule
      change combineOccurrence splitter ∈
        (aggregateAfterSplitSchedule splitter).finalAvailability
      unfold aggregateAfterSplitSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_self

def splitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .value)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.mask (inputs .value) (inputs .mask) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (layerChildren : (child : (aggregateBody splitter).context.instancePorts.Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (aggregateChildContracts splitter child))

private abbrev aggregateCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (aggregateBody splitter) layerChildren

private def aggregateStateCorresponds
    (_ : (cycleContract splitter.aggregateType).state.Values)
    (_ : (aggregateCertificationStructure splitter layerChildren).State) : Prop := True

private theorem aggregateImplements :
    Contracts.Cycle.Implements
      (aggregateCertificationStructure splitter layerChildren)
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton
      (child : (aggregateBody splitter).context.instancePorts.Name) :
      Subsingleton
        ((aggregateChildContracts splitter child).state.Values) := by
    cases child with
    | splitter recursiveInput =>
        cases recursiveInput
        change Subsingleton emptySignalMap.Values
        infer_instance
    | component component =>
        change Subsingleton emptySignalMap.Values
        infer_instance
    | combiner output =>
        cases output
        change Subsingleton emptySignalMap.Values
        infer_instance
  have childMatch (child : (aggregateBody splitter).context.instancePorts.Name) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
        proposal satisfies child (by cases child <;> exact SignalMap.emptyValues)
  rcases proposal with ⟨outputs, childProposals⟩
  have boundary := satisfies.1
  have splitOutputs : (childProposals (.splitter .unit)).outputs =
      splitter.outputValues (splitterInputs splitter inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (.splitter .unit)).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure))
        inputs childProposals (.splitter .unit) = splitterInputs splitter inputs := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have componentOutputs : ∀ component,
      (childProposals (.component component)).outputs .result =
        (splitter.ports.outputs.signalType component).mask
          (splitter.outputValues (splitterInputs splitter inputs) component)
          (inputs .mask) := by
    intro component
    have evaluates := (childMatch (.component component)).1
    have holds := evaluates.1 Rule.apply
    change (outputRule (splitter.ports.outputs.signalType component)).Holds
      _ _ _ at holds
    rw [outputRule_holds_iff] at holds
    have valueInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.component component)) .value =
      splitter.outputValues (splitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun splitOutputs component
    have maskInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.component component)) .mask = inputs .mask := by
      cases splitter <;> rfl
    exact holds.trans (by rw [valueInput, maskInput])
  have combineOutputs : (childProposals (.combiner .result)).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.combiner .result)) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff splitter.combiner _ _ _).mp
      ((childMatch (.combiner .result)).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result =
      splitter.aggregateType.mask (inputs .value) (inputs .mask)
    cases splitter with
    | vector length element =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs Composition.AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs Composition.AggregatePort.value]
        change (fun component =>
          (childProposals (.component component)).outputs .result) = _
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs Composition.AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs Composition.AggregatePort.value]
        change fields.assemble (fun component =>
          (childProposals (.component component)).outputs .result) =
            fields.mask (inputs .value) (inputs .mask)
        rw [← fields.assemble_get (fields.mask (inputs .value) (inputs .mask))]
        apply congrArg fields.assemble
        funext component
        exact (componentOutputs component).trans
          (fields.get_mask (inputs .value) (inputs .mask) component).symm
  · rfl

end AggregateLayerCertification

noncomputable opaque aggregateCertifiedLayer
    (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (cycleContract splitter.aggregateType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (aggregateRuleSchedules splitter) (aggregateCoversChildren splitter)
    (aggregateStateCorresponds splitter)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (aggregateImplements splitter)

@[reducible] noncomputable def aggregateCertifiedChildren
    (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (child : (aggregateBody splitter).context.instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter child)
  | .splitter _ =>
      ⟨.splitter splitter, splitter.certified.certification⟩
  | .component component =>
      ⟨moduleStructure (splitter.ports.outputs.signalType component),
        components component⟩
  | .combiner _ =>
      ⟨.combiner splitter.combiner, splitter.combiner.certified.certification⟩

noncomputable def aggregateImplementation (splitter : Composition.SignalSplitter)
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
    cases splitter with
    | vector length element =>
        rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_2]
        congr
        funext child
        cases child <;> rfl
    | tuple fields =>
        rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_3]
        congr
        funext child
        cases child <;> rfl
  exact instantiated.certification.transportStructure sameStructure

private noncomputable def implementationDefinition :
    (signalType : SignalType) → Implementation signalType
  | .bit => bitImplementation
  | .vector length element =>
      aggregateImplementation (.vector length element) fun _ =>
        implementationDefinition element
  | .tuple fields =>
      aggregateImplementation (.tuple fields) fun component =>
        implementationDefinition (fields.typeAt component)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

noncomputable opaque implementation (signalType : SignalType) :
    Implementation signalType :=
  implementationDefinition signalType

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  rfl

end Silean.Modules.Mask

namespace Silean.Modules.Mask.Naming

open Silean Silean.Naming

private def indexedComponent (signals : SignalMap) (component : signals.Label) :
    SourceName :=
  .scoped "mask" ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Mask.ports signalType) where
  inputs := ⟨fun | .value => "value" | .mask => "mask"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => typeNaming | .mask => .bit
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.Mask.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Mask.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Mask.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_1]
      unfold Modules.Mask.bitModuleStructure
      exact .composite ⟨"mask", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean.Naming.Primitive.and)
  | .vector length element, typeNaming => by
      rw [Modules.Mask.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_2]
      let splitter : Composition.SignalSplitter := .vector length element
      exact .composite ⟨"mask", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .result => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component => namingWith element (typeNaming.component component)
          | .combiner .result => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.Mask.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_3]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"mask", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .result => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .combiner .result => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Mask.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.Mask.Naming
