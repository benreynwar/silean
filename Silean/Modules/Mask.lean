import Silean.CertifiedSchedule
import Silean.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.And
import Silean.SignalLogic

namespace Silean.Modules.Mask

open Silean

inductive Input | value | mask
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def interface : LeafwiseInterface where
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
    CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons .bit .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((inputMap signalType).select .mask).prepend .value
  writesOutputs := (outputMap signalType).select .result
  target | (value, (mask, ())), _ => (signalType.mask value mask, ())

@[reducible] def cycleContract (signalType : SignalType) :
    ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

/-! The bit specialization is a readable wrapper around the closed AND
primitive. -/

inductive BitInstance | gate
deriving Enumeration

@[reducible] def bitInstances : Instances :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.and.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instances := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instances where
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  instanceInput
    | .gate, .left => bitContext.moduleInput .value
    | .gate, .right => bitContext.moduleInput .mask

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildren : Certified.Children bitBody
  | .gate => Primitives.andCertified

def bitModuleStructure : ModuleStructure (ports .bit) :=
  Certified.moduleStructure bitBody bitChildren

abbrev bitRule : Certified.RuleOccurrence bitChildren :=
  ⟨.gate, Primitives.AndRule.apply⟩

def bitOutputSchedule : Certified.OutputSchedule bitBody bitChildren
    (cycleContract .bit) .apply :=
  .call bitRule
    (by
      intro input member
      cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
          bitBody, bitWiring,
          bitContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output member
      cases output
      exact ⟨Primitives.AndRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Certified.StateSchedule bitBody bitChildren :=
  .done (by
    intro child input member
    cases child
    simp [bitChildren, Primitives.andCertified, Primitives.andCycleContract,
      CycleStateRule.empty, SignalSelection.labels] at member)

def bitRuleSchedules : Certified.RuleSchedules bitBody bitChildren
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.AndRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs bitRuleSchedules .apply
  change bitRule ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule, Certified.Schedule.finalAvailability]

theorem bitHasAtMostOneSolution : bitModuleStructure.HasAtMostOneSolution :=
  bitRuleSchedules.hasAtMostOneSolution bitCoversChildren

def bitGateInputs (inputs : (ports .bit).inputs.Values) :
    Primitives.and.ports.inputs.Values
  | .left => inputs .value
  | .right => inputs .mask

theorem bitHasStructuralResult (inputs : (ports .bit).inputs.Values)
    (state : bitModuleStructure.State) :
    ∃ proposal, bitModuleStructure.IsSolution inputs state proposal := by
  rcases Primitives.andCertified.hasStructuralResult
      (bitGateInputs inputs) (state .gate) with ⟨gate, gateSatisfies⟩
  let children : (name : BitInstance) →
      ProposedValues (Certified.childStructure bitChildren name)
    | .gate => gate
  let outputs : (ports .bit).outputs.Values := fun
    | .result => gate.outputs .output
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child
    change Primitives.andCertified.moduleStructure.IsSolution
      (ProposedValues.childInputs bitBody (Certified.childStructure bitChildren)
        inputs children .gate) (state .gate) gate
    rw [show ProposedValues.childInputs bitBody
      (Certified.childStructure bitChildren) inputs children .gate =
        bitGateInputs inputs by funext port; cases port <;> rfl]
    exact gateSatisfies

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : bitModuleStructure.State) : Prop := True

private theorem bitImplements : Implements bitModuleStructure
    (cycleContract .bit) emptyStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have gateImplements := Certified.childImplements bitChildren inputs
    structuralState proposal satisfies .gate SignalMap.emptyValues (by trivial)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [show (outputRule .bit).Holds inputs contractState proposal.outputs ↔
        proposal.outputs .result = (inputs .value && inputs .mask) by
      simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
        SignalSelection.project, SignalSelection.prepend, SignalMap.select,
        SignalType.mask]]
    rcases proposal with ⟨outputs, children⟩
    change outputs .result = (inputs .value && inputs .mask)
    rcases gateImplements with ⟨_, gateEvaluates, _⟩
    have boundaryResult := boundary .result
    change outputs .result = (children .gate).outputs .output at boundaryResult
    have gateInputs : ProposedValues.childInputs bitBody
        (Certified.childStructure bitChildren) inputs children .gate =
          bitGateInputs inputs := by
      funext port
      cases port <;> rfl
    have gateOutput : (children .gate).outputs .output =
        (inputs .value && inputs .mask) := by
      have contractOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
        (gateEvaluates.1 Primitives.AndRule.apply)
      rw [gateInputs] at contractOutput
      exact contractOutput
    exact boundaryResult.trans gateOutput
  · rfl

@[reducible] def aggregateBody (splitter : SignalSplitter) :=
  interface.aggregateBody splitter

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  := interface.moduleStructure bitModuleStructure

structure Implementation (signalType : SignalType)
    (moduleStructure : ModuleStructure (ports signalType)) where
  hasStructuralResult : ∀ inputs state,
    ∃ proposal, moduleStructure.IsSolution inputs state proposal
  structuralResultUnique : moduleStructure.HasAtMostOneSolution
  implements : Implements moduleStructure (cycleContract signalType)
    (fun _ _ => True)

def Implementation.certified
    {moduleStructure : ModuleStructure (ports signalType)}
    (implementation : Implementation signalType moduleStructure) :
    ModuleCycleCertified (ports signalType) where
  moduleStructure := moduleStructure
  cycleContract := cycleContract signalType
  certification := {
    stateCorresponds := fun _ _ => True,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := implementation.hasStructuralResult,
    structuralResultUnique := implementation.structuralResultUnique,
    implements := implementation.implements }

abbrev CanonicalImplementation (signalType : SignalType) :=
  Implementation signalType (moduleStructure signalType)

theorem moduleStructure_bit : moduleStructure .bit = bitModuleStructure := by
  rw [moduleStructure, LeafwiseInterface.moduleStructure.eq_1]

theorem bitImplementation : CanonicalImplementation .bit where
  hasStructuralResult := by
    rw [moduleStructure_bit]
    exact bitHasStructuralResult
  structuralResultUnique := by
    rw [moduleStructure_bit]
    exact bitHasAtMostOneSolution
  implements := by
    rw [moduleStructure_bit]
    exact bitImplements

@[reducible] def aggregateChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.Children (aggregateBody splitter) :=
  interface.aggregateChildren splitter fun component =>
    (components component).certified

@[reducible] def aggregateChildStructure (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :=
  Certified.childStructure (aggregateChildren splitter components)

theorem aggregateModuleStructure_eq (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    moduleStructure splitter.aggregateType =
      Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components) := by
  cases splitter with
  | vector length element =>
      rw [moduleStructure, LeafwiseInterface.moduleStructure.eq_2]
      simp only [SignalSplitter.aggregateType, Certified.moduleStructure]
      congr
      funext child
      cases child <;> rfl
  | tuple fields =>
      rw [moduleStructure, LeafwiseInterface.moduleStructure.eq_3]
      simp only [SignalSplitter.aggregateType, Certified.moduleStructure]
      congr
      funext child
      cases child <;> rfl

def splitterInputs (splitter : SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .value)

def componentInputs (splitter : SignalSplitter)
    (splitProposal : ProposedValues splitter.certified.moduleStructure)
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values
  | .value => splitProposal.outputs component
  | .mask => inputs .mask

def combinerInputs (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component))
    (proposals : (component : splitter.ports.outputs.Label) →
      ProposedValues (moduleStructure
        (splitter.ports.outputs.signalType component))) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter <;> exact fun component => (proposals component).outputs .result

def aggregateOutputs (splitter : SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .result => combineProposal.outputs .value
  | .tuple _ => fun | .result => combineProposal.outputs .value

def aggregateProposalConstruction (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    interface.AggregateProposalConstruction splitter
      (fun component => (components component).certified) where
  splitterInputs inputs _ := splitterInputs splitter inputs
  componentInputs inputs splitProposals component :=
    componentInputs splitter (splitProposals .unit) inputs component
  combinerInputs componentProposals _ :=
    combinerInputs splitter components componentProposals
  outputs combineProposals := aggregateOutputs splitter (combineProposals .result)
  boundary_eq := by
    intro inputs splitProposals componentProposals combineProposals output
    cases output
    cases splitter <;> rfl
  splitterInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals recursiveInput
    cases recursiveInput
    cases splitter <;> funext port <;> cases port <;> rfl
  componentInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals component
    cases splitter <;> funext port <;> cases port <;> rfl
  combinerInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals output
    cases output
    cases splitter <;> funext port <;> rfl

theorem aggregateHasStructuralResult (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (state : (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).IsSolution inputs state proposal := by
  exact (aggregateProposalConstruction splitter components).hasStructuralResult inputs state

abbrev splitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  interface.splitterOccurrence splitter
    (fun component => (components component).certified) .unit

abbrev componentOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  interface.componentOccurrence splitter
    (fun component => (components component).certified) component Rule.apply

abbrev combineOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  interface.combinerOccurrence splitter
    (fun component => (components component).certified) .result

@[simp] theorem splitOccurrence_writes (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    (splitOccurrence splitter components).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

noncomputable def componentSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [splitOccurrence splitter components] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter components component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [splitOccurrence splitter components] ∨
          ∃ component, called = componentOccurrence splitter components component)
      [splitOccurrence splitter components] :=
  interface.callComponentsAfter splitter
    (fun component => (components component).certified)
    ([splitOccurrence splitter components] : Certified.Availability
      (aggregateChildren splitter components))
    (fun _ => Rule.apply)
    (by
      intro component member
      simp only [List.mem_singleton] at member
      have childEqual := congrArg Certified.RuleOccurrence.child member
      cases childEqual)
    (by
      intro component input member
      cases input with
      | value =>
          cases splitter with
          | vector length element =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (splitOccurrence (.vector length element) components).writes
                  rw [splitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (splitOccurrence (.tuple fields) components).writes
                  rw [splitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
      | mask =>
          cases splitter <;>
            simp [outputRule, SignalSelection.prepend, SignalMap.select,
              SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
              LeafwiseInterface.aggregateWiring,
              LeafwiseInterface.aggregateComponentInputSource,
              LeafwiseInterface.aggregateContext,
              LeafwiseInterface.aggregateInstances, interface,
              LeafwiseInterface.inputType, EndpointContext.moduleInput])

theorem aggregateBoundaryReady (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component))
    {available : Certified.Availability (aggregateChildren splitter components)}
    (combineAvailable : combineOccurrence splitter components ∈ available) :
    Certified.BoundaryReady (aggregateBody splitter)
      (aggregateChildren splitter components)
      ((outputRule splitter.aggregateType).writesOutputs.labels)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      available := by
  intro output member
  cases output
  cases splitter <;>
    exact ⟨SignalComponentRule.apply, combineAvailable,
      by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩

noncomputable def aggregateAfterSplitSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Certified.BoundaryReady (aggregateBody splitter)
        (aggregateChildren splitter components)
        (outputRule splitter.aggregateType).writesOutputs.labels
        (fun input => input ∈
          (outputRule splitter.aggregateType).readsInputs.labels))
      [splitOccurrence splitter components] := by
  apply (componentSchedule splitter components).append
  refine .call (combineOccurrence splitter components) ?_ ?_ (.done ?_)
  · intro input member
    cases splitter <;>
      exact ⟨Rule.apply,
        (componentSchedule _ components).finished.2.1 input,
        by change Output.result ∈ [Output.result]; simp⟩
  · intro present
    rcases (componentSchedule splitter components).finished.2.2 _ present with
      atStart | fromComponent
    · simp only [List.mem_singleton] at atStart
      have childEqual := congrArg Certified.RuleOccurrence.child atStart
      cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      cases equal
  · exact aggregateBoundaryReady splitter components (by simp)

noncomputable def aggregateOutputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .apply := by
  refine .call (splitOccurrence splitter components) ?_ (by simp) ?_
  · intro input member
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
        LeafwiseInterface.aggregateWiring,
        LeafwiseInterface.aggregateSplitterInputSource,
        LeafwiseInterface.aggregateContext,
        LeafwiseInterface.aggregateInstances, interface,
        LeafwiseInterface.inputType, EndpointContext.moduleInput]
  · exact aggregateAfterSplitSchedule splitter components

def aggregateStateSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) :=
  .done (by
    intro child input member
    cases child <;>
      simp [aggregateChildren, LeafwiseInterface.aggregateChildren,
        Implementation.certified, cycleContract,
        SignalSplitter.certified, SignalSplitter.cycleContract,
        SignalCombiner.certified, SignalCombiner.cycleContract,
        CycleStateRule.empty, SignalSelection.labels] at member)

noncomputable def aggregateRuleSchedules (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType) where
  output | .apply => aggregateOutputSchedule splitter components
  state := aggregateStateSchedule splitter components

theorem split_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    splitOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change splitOccurrence splitter components ∈
    (aggregateAfterSplitSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.1 _ (by simp))

theorem component_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter components component ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change componentOccurrence splitter components component ∈
    (aggregateAfterSplitSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.2.1 component)

theorem combine_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    combineOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change combineOccurrence splitter components ∈
    (aggregateAfterSplitSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_self

theorem aggregateCoversChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    (aggregateRuleSchedules splitter components).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (aggregateRuleSchedules splitter components) .apply
  cases child with
  | splitter recursiveInput =>
      cases recursiveInput
      change SignalComponentRule at rule
      cases rule
      exact split_mem_outputSchedule splitter components
  | component component =>
      change Rule at rule
      cases rule
      exact component_mem_outputSchedule splitter components component
  | combiner output =>
      cases output
      change SignalComponentRule at rule
      cases rule
      exact combine_mem_outputSchedule splitter components

theorem aggregateHasAtMostOneSolution (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).HasAtMostOneSolution :=
  (aggregateRuleSchedules splitter components).hasAtMostOneSolution
    (aggregateCoversChildren splitter components)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.mask (inputs .value) (inputs .mask) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

private theorem aggregateImplements (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    Implements
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have splitOutputs : (childProposals (.splitter .unit)).outputs =
      splitter.outputValues (splitterInputs splitter inputs) := by
    cases splitter <;> exact childSatisfies (.splitter .unit)
  have componentOutputs : ∀ component,
      (childProposals (.component component)).outputs .result =
        (splitter.ports.outputs.signalType component).mask
          (splitter.outputValues (splitterInputs splitter inputs) component)
          (inputs .mask) := by
    intro component
    rcases (components component).implements
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.component component))
        SignalMap.emptyValues (structuralState (.component component))
        (childProposals (.component component)) trivial
        (childSatisfies (.component component)) with
      ⟨nextState, evaluates, nextCorresponds⟩
    have holds := evaluates.1 Rule.apply
    rw [outputRule_holds_iff] at holds
    have valueInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.component component)) .value =
      splitter.outputValues (splitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun splitOutputs component
    have maskInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.component component)) .mask = inputs .mask := by
      cases splitter <;> rfl
    exact holds.trans (by rw [valueInput, maskInput])
  have combineOutputs : (childProposals (.combiner .result)).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.combiner .result)) := by cases splitter <;> exact childSatisfies (.combiner .result)
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
          (childProposals (.combiner .result)).outputs AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs AggregatePort.value]
        change (fun component =>
          (childProposals (.component component)).outputs .result) = _
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs AggregatePort.value]
        change fields.assemble (fun component =>
          (childProposals (.component component)).outputs .result) =
            fields.mask (inputs .value) (inputs .mask)
        rw [← fields.assemble_get (fields.mask (inputs .value) (inputs .mask))]
        apply congrArg fields.assemble
        funext component
        exact (componentOutputs component).trans
          (fields.get_mask (inputs .value) (inputs .mask) component).symm
  · rfl

theorem aggregateImplementation (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      CanonicalImplementation (splitter.ports.outputs.signalType component)) :
    CanonicalImplementation splitter.aggregateType where
  hasStructuralResult := by
    rw [aggregateModuleStructure_eq splitter components]
    exact aggregateHasStructuralResult splitter components
  structuralResultUnique := by
    rw [aggregateModuleStructure_eq splitter components]
    exact aggregateHasAtMostOneSolution splitter components
  implements := by
    rw [aggregateModuleStructure_eq splitter components]
    exact aggregateImplements splitter components

private theorem implementationDefinition :
    (signalType : SignalType) → CanonicalImplementation signalType
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
    CanonicalImplementation signalType :=
  implementationDefinition signalType

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) := (implementation signalType).certified

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
        LeafwiseInterface.moduleStructure.eq_1]
      unfold Modules.Mask.bitModuleStructure Certified.moduleStructure
      exact .composite ⟨"mask", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean.Naming.Primitive.and)
  | .vector length element, typeNaming => by
      rw [Modules.Mask.moduleStructure,
        LeafwiseInterface.moduleStructure.eq_2]
      let splitter : SignalSplitter := .vector length element
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
        LeafwiseInterface.moduleStructure.eq_3]
      let splitter : SignalSplitter := .tuple fields
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
