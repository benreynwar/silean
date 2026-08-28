import Silean.Contracts.Cycle.CycleSchedule
import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Or
import Silean.Composition.SignalLogic

namespace Silean.Modules.BitwiseOr

open Silean

/-! Generic bitwise OR. Aggregate signal types are implemented recursively
from the one-bit OR primitive. -/

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def interface : Composition.LeafwiseInterface where
  Input := Input
  inputs := inferInstance
  RecursiveInput := Input
  recursiveInputs := inferInstance
  FixedInput := NoSignal
  fixedInputs := inferInstance
  inputLayout := {
    classify := fun input => .inl input
    label := fun | .inl input => input | .inr impossible => nomatch impossible
    classify_label := by
      intro part
      cases part with
      | inl input => rfl
      | inr impossible => exact nomatch impossible
    label_classify := by intro input; rfl }
  fixedInputType := fun impossible => nomatch impossible
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
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((inputMap signalType).select .right).prepend .left
  writesOutputs := (outputMap signalType).select .result
  target | (left, (right, ())), _ => (signalType.bitwiseOr left right, ())

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

/-! ## Hardware structure

The bit specialization is a readable wrapper around the closed OR
primitive. -/

inductive BitInstance
  /-- The one-bit OR primitive. -/
  | gate
deriving Enumeration

@[reducible] def bitInstances : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.or.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instancePorts where
  -- The gate result is the bitwise-OR result.
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  -- Both operands feed the OR gate.
  instanceInput
    | .gate, .left => bitContext.moduleInput .left
    | .gate, .right => bitContext.moduleInput .right

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildren : Contracts.Cycle.Certification.Children bitBody
  | .gate => Primitives.orCertified

def bitModuleStructure : ModuleStructure (ports .bit) :=
  Contracts.Cycle.Certification.moduleStructure bitBody bitChildren

abbrev bitRule : Contracts.Cycle.Certification.RuleOccurrence bitChildren :=
  ⟨.gate, Primitives.OrRule.apply⟩

def bitOutputSchedule : Contracts.Cycle.Certification.OutputSchedule bitBody bitChildren
    (cycleContract .bit) .apply :=
  .call bitRule
    (by
      intro input member
      cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
          bitBody, bitWiring,
          bitContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output member
      cases output
      exact ⟨Primitives.OrRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Contracts.Cycle.Certification.StateSchedule bitBody bitChildren :=
  .done (by
    intro child input member
    cases child
    simp [bitChildren, Primitives.orCertified, Primitives.orCycleContract,
      Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

def bitRuleSchedules : Contracts.Cycle.Certification.RuleSchedules bitBody bitChildren
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.OrRule at rule
  cases rule
  apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
  apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs bitRuleSchedules .apply
  change bitRule ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

theorem bitHasAtMostOneSolution : bitModuleStructure.HasAtMostOneSolution :=
  bitRuleSchedules.hasAtMostOneSolution bitCoversChildren

def bitGateInputs (inputs : (ports .bit).inputs.Values) :
    Primitives.or.ports.inputs.Values
  | .left => inputs .left
  | .right => inputs .right

theorem bitHasStructuralResult (inputs : (ports .bit).inputs.Values)
    (state : bitModuleStructure.State) :
    ∃ proposal, bitModuleStructure.IsSolution inputs state proposal := by
  rcases Primitives.orCertified.hasStructuralResult
      (bitGateInputs inputs) (state .gate) with ⟨gate, gateSatisfies⟩
  let children : (name : BitInstance) →
      ProposedValues (Contracts.Cycle.Certification.childStructure bitChildren name)
    | .gate => gate
  let outputs : (ports .bit).outputs.Values := fun
    | .result => gate.outputs .output
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child
    change Primitives.orCertified.moduleStructure.IsSolution
      (ProposedValues.childInputs bitBody (Contracts.Cycle.Certification.childStructure bitChildren)
        inputs children .gate) (state .gate) gate
    rw [show ProposedValues.childInputs bitBody
      (Contracts.Cycle.Certification.childStructure bitChildren) inputs children .gate =
        bitGateInputs inputs by funext port; cases port <;> rfl]
    exact gateSatisfies

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : bitModuleStructure.State) : Prop := True

private theorem bitImplements : Contracts.Cycle.Implements bitModuleStructure
    (cycleContract .bit) emptyStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [show (outputRule .bit).Holds inputs contractState proposal.outputs ↔
        proposal.outputs .result = (inputs .left || inputs .right) by
      simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
        SignalSelection.project, SignalSelection.prepend, SignalMap.select,
        SignalType.bitwiseOr]]
    rcases proposal with ⟨outputs, children⟩
    rcases satisfies with ⟨boundary, childSatisfies⟩
    change outputs .result = (inputs .left || inputs .right)
    have gate := childSatisfies .gate
    have boundaryResult := boundary .result
    change outputs .result = (children .gate).outputs .output at boundaryResult
    have gateInputs : ProposedValues.childInputs bitBody
        (Contracts.Cycle.Certification.childStructure bitChildren) inputs children .gate =
          bitGateInputs inputs := by
      funext port
      cases port <;> rfl
    have gateOutput : (children .gate).outputs .output =
        (inputs .left || inputs .right) := by
      have structural := gate.1
      rw [gateInputs] at structural
      exact congrFun structural .output
    exact boundaryResult.trans gateOutput
  · rfl

@[reducible] def aggregateBody (splitter : Composition.SignalSplitter) :=
  interface.aggregateBody splitter

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  := interface.moduleStructure bitModuleStructure

abbrev Implementation (signalType : SignalType) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

def Implementation.certified (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

theorem moduleStructure_bit : moduleStructure .bit = bitModuleStructure := by
  rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_1]

def bitImplementation : Implementation .bit where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := by
    rw [moduleStructure_bit]
    exact bitHasStructuralResult
  structuralResultUnique := by
    rw [moduleStructure_bit]
    exact bitHasAtMostOneSolution
  implements := by
    rw [moduleStructure_bit]
    exact bitImplements

@[reducible] def aggregateChildren (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.Children (aggregateBody splitter) :=
  interface.aggregateChildren splitter fun component =>
    (components component).certified

@[reducible] def aggregateChildStructure (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :=
  Contracts.Cycle.Certification.childStructure (aggregateChildren splitter components)

theorem aggregateModuleStructure_eq (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    moduleStructure splitter.aggregateType =
      Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components) := by
  cases splitter with
  | vector length element =>
      rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_2]
      simp only [Composition.SignalSplitter.aggregateType, Contracts.Cycle.Certification.moduleStructure]
      congr
      funext child
      cases child with
      | splitter input => cases input <;> rfl
      | component component => rfl
      | combiner output => cases output; rfl
  | tuple fields =>
      rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_3]
      simp only [Composition.SignalSplitter.aggregateType, Contracts.Cycle.Certification.moduleStructure]
      congr
      funext child
      cases child with
      | splitter input => cases input <;> rfl
      | component component => rfl
      | combiner output => cases output; rfl

def leftSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .left)

def rightSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .right)

def componentInputs (splitter : Composition.SignalSplitter)
    (leftSplit rightSplit : ProposedValues splitter.certified.moduleStructure)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values
  | .left => leftSplit.outputs component
  | .right => rightSplit.outputs component

def combinerInputs (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (proposals : (component : splitter.ports.outputs.Label) →
      ProposedValues
        (moduleStructure (splitter.ports.outputs.signalType component))) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter <;> exact fun component => (proposals component).outputs .result

def aggregateOutputs (splitter : Composition.SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .result => combineProposal.outputs .value
  | .tuple _ => fun | .result => combineProposal.outputs .value

def aggregateProposalConstruction (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    interface.AggregateProposalConstruction splitter
      (fun component => (components component).certified) where
  splitterInputs inputs
    | .left => leftSplitterInputs splitter inputs
    | .right => rightSplitterInputs splitter inputs
  componentInputs _ splitProposals component :=
    componentInputs splitter (splitProposals .left) (splitProposals .right) component
  combinerInputs componentProposals _ :=
    combinerInputs splitter components componentProposals
  outputs combineProposals := aggregateOutputs splitter (combineProposals .result)
  boundary_eq := by
    intro inputs splitProposals componentProposals combineProposals output
    cases output
    cases splitter <;> rfl
  splitterInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals recursiveInput
    cases recursiveInput <;> cases splitter <;>
      funext port <;> cases port <;> rfl
  componentInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals component
    cases splitter <;> funext port <;> cases port <;> rfl
  combinerInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals output
    cases output
    cases splitter <;> funext port <;> rfl

theorem aggregateHasStructuralResult (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (state : (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).IsSolution inputs state proposal := by
  exact (aggregateProposalConstruction splitter components).hasStructuralResult inputs state

abbrev leftSplitOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.splitterOccurrence splitter
    (fun component => (components component).certified) .left

abbrev rightSplitOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.splitterOccurrence splitter
    (fun component => (components component).certified) .right

abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.componentOccurrence splitter
    (fun component => (components component).certified) component Rule.apply

abbrev combineOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.combinerOccurrence splitter
    (fun component => (components component).certified) .result

@[simp] theorem leftSplitOccurrence_writes (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (leftSplitOccurrence splitter components).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

@[simp] theorem rightSplitOccurrence_writes (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (rightSplitOccurrence splitter components).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

noncomputable def componentSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈
          [rightSplitOccurrence splitter components,
            leftSplitOccurrence splitter components] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter components component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [rightSplitOccurrence splitter components,
            leftSplitOccurrence splitter components] ∨
          ∃ component, called = componentOccurrence splitter components component)
      [rightSplitOccurrence splitter components,
        leftSplitOccurrence splitter components] :=
  interface.callComponentsAfter splitter
    (fun component => (components component).certified)
    ([rightSplitOccurrence splitter components,
      leftSplitOccurrence splitter components] : Contracts.Cycle.Certification.Availability
      (aggregateChildren splitter components))
    (fun _ => Rule.apply)
    (by
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg Contracts.Cycle.Certification.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro component input member
      cases input with
      | left =>
          cases splitter with
          | vector length element =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (leftSplitOccurrence (.vector length element) components).writes
                  rw [leftSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (leftSplitOccurrence (.tuple fields) components).writes
                  rw [leftSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
      | right =>
          cases splitter with
          | vector length element =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (rightSplitOccurrence (.vector length element) components).writes
                  rw [rightSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (rightSplitOccurrence (.tuple fields) components).writes
                  rw [rightSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩)

theorem aggregateBoundaryReady (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    {available : Contracts.Cycle.Certification.Availability (aggregateChildren splitter components)}
    (combineAvailable : combineOccurrence splitter components ∈ available) :
    Contracts.Cycle.Certification.BoundaryReady (aggregateBody splitter)
      (aggregateChildren splitter components)
      ((outputRule splitter.aggregateType).writesOutputs.labels)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      available := by
  intro output member
  cases output
  cases splitter <;>
    exact ⟨Composition.SignalComponentRule.apply, combineAvailable,
      by change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]; simp⟩

noncomputable def aggregateAfterSplitsSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Contracts.Cycle.Certification.BoundaryReady (aggregateBody splitter)
        (aggregateChildren splitter components)
        (outputRule splitter.aggregateType).writesOutputs.labels
        (fun input => input ∈
          (outputRule splitter.aggregateType).readsInputs.labels))
      [rightSplitOccurrence splitter components,
        leftSplitOccurrence splitter components] := by
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
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at atStart
      rcases atStart with equal | equal <;>
        have childEqual := congrArg Contracts.Cycle.Certification.RuleOccurrence.child equal <;>
        cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      cases equal
  · exact aggregateBoundaryReady splitter components (by simp)

noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .apply := by
  refine .call (leftSplitOccurrence splitter components) ?_ (by simp) ?_
  · intro input member
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable, aggregateBody,
        Composition.LeafwiseInterface.aggregateWiring,
        Composition.LeafwiseInterface.aggregateSplitterInputSource,
        Composition.LeafwiseInterface.aggregateContext,
        Composition.LeafwiseInterface.aggregateInstances, interface,
        Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput]
  · refine .call (rightSplitOccurrence splitter components) ?_
      (by
        intro member
        simp only [List.mem_singleton] at member
        have childEqual := congrArg Contracts.Cycle.Certification.RuleOccurrence.child member
        have inputEqual : Input.right = Input.left := by injection childEqual
        cases inputEqual) ?_
    · intro input member
      cases splitter <;> cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable, aggregateBody,
          Composition.LeafwiseInterface.aggregateWiring,
          Composition.LeafwiseInterface.aggregateSplitterInputSource,
          Composition.LeafwiseInterface.aggregateContext,
          Composition.LeafwiseInterface.aggregateInstances, interface,
          Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput]
    · exact aggregateAfterSplitsSchedule splitter components

def aggregateStateSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) :=
  .done (by
    intro child input member
    cases child with
    | splitter recursiveInput =>
        cases recursiveInput <;>
        simp [aggregateChildren, Composition.LeafwiseInterface.aggregateChildren,
          Composition.SignalSplitter.certified,
          Composition.SignalSplitter.cycleContract, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | component component =>
        simp [aggregateChildren, Composition.LeafwiseInterface.aggregateChildren,
          Implementation.certified,
          Contracts.Cycle.ModuleCycleCertification.bundle, cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member
    | combiner output =>
        cases output
        simp [aggregateChildren, Composition.LeafwiseInterface.aggregateChildren,
          Composition.SignalCombiner.certified,
          Composition.SignalCombiner.cycleContract, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member)

noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType) where
  output | .apply => aggregateOutputSchedule splitter components
  state := aggregateStateSchedule splitter components

theorem leftSplit_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    leftSplitOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change leftSplitOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.1 _ (by simp))

theorem rightSplit_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    rightSplitOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change rightSplitOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.1 _ (by simp))

theorem component_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter components component ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change componentOccurrence splitter components component ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.2.1 component)

theorem combine_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    combineOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change combineOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
  exact List.mem_cons_self

theorem aggregateCoversChildren (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (aggregateRuleSchedules splitter components).CoversChildren := by
  intro child rule
  apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
  apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs
    (aggregateRuleSchedules splitter components) .apply
  cases child with
  | splitter recursiveInput =>
      cases recursiveInput with
      | left =>
          change Composition.SignalComponentRule at rule
          cases rule
          exact leftSplit_mem_outputSchedule splitter components
      | right =>
          change Composition.SignalComponentRule at rule
          cases rule
          exact rightSplit_mem_outputSchedule splitter components
  | component component =>
      change Rule at rule
      cases rule
      exact component_mem_outputSchedule splitter components component
  | combiner output =>
      cases output
      change Composition.SignalComponentRule at rule
      cases rule
      exact combine_mem_outputSchedule splitter components

theorem aggregateHasAtMostOneSolution (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).HasAtMostOneSolution :=
  (aggregateRuleSchedules splitter components).hasAtMostOneSolution
    (aggregateCoversChildren splitter components)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.bitwiseOr (inputs .left) (inputs .right) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

private theorem aggregateImplements (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have leftSplitOutputs : (childProposals (.splitter .left)).outputs =
      splitter.outputValues (leftSplitterInputs splitter inputs) := by
    cases splitter <;> exact childSatisfies (.splitter .left)
  have rightSplitOutputs :
      (childProposals ((.splitter .right))).outputs =
        splitter.outputValues (rightSplitterInputs splitter inputs) := by
    cases splitter <;> exact childSatisfies ((.splitter .right))
  have componentOutputs : ∀ component,
      (childProposals ((.component component))).outputs .result =
        (splitter.ports.outputs.signalType component).bitwiseOr
          (splitter.outputValues (leftSplitterInputs splitter inputs) component)
          (splitter.outputValues (rightSplitterInputs splitter inputs) component) := by
    intro component
    rcases (components component).hasCorrespondingState
        (structuralState ((.component component))) with
      ⟨componentState, componentCorresponds⟩
    have componentState_eq : componentState = SignalMap.emptyValues :=
      by
        funext statePort
        exact nomatch statePort
    subst componentState
    rcases (components component).implements
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          ((.component component)))
        SignalMap.emptyValues (structuralState ((.component component)))
        (childProposals ((.component component))) componentCorresponds
        (childSatisfies ((.component component))) with
      ⟨nextState, evaluates, nextCorresponds⟩
    have holds := evaluates.1 Rule.apply
    rw [outputRule_holds_iff] at holds
    have leftInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          ((.component component))) .left =
      splitter.outputValues (leftSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          ((.component component))) .right =
      splitter.outputValues (rightSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact holds.trans (by rw [leftInput, rightInput])
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
      splitter.aggregateType.bitwiseOr (inputs .left) (inputs .right)
    cases splitter with
    | vector length element =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs Composition.AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs Composition.AggregatePort.value]
        change (fun component =>
          (childProposals ((.component component))).outputs .result) = _
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs Composition.AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs Composition.AggregatePort.value]
        change fields.assemble (fun component =>
          (childProposals ((.component component))).outputs .result) =
            fields.bitwiseOr (inputs .left) (inputs .right)
        rw [← fields.assemble_get (fields.bitwiseOr (inputs .left) (inputs .right))]
        apply congrArg fields.assemble
        funext component
        exact (componentOutputs component).trans
          (fields.get_bitwiseOr (inputs .left) (inputs .right) component).symm
  · rfl

noncomputable def aggregateCertification (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := aggregateHasStructuralResult splitter components
  structuralResultUnique := aggregateHasAtMostOneSolution splitter components
  implements := aggregateImplements splitter components

noncomputable def aggregateImplementation (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implementation splitter.aggregateType :=
  (aggregateCertification splitter components).transportStructure
    (aggregateModuleStructure_eq splitter components).symm

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

end Silean.Modules.BitwiseOr

namespace Silean.Modules.BitwiseOr.Naming

open Silean Silean.Naming

private def indexedComponent (signals : SignalMap) (component : signals.Label) :
    SourceName :=
  .scoped "or" ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.BitwiseOr.ports signalType) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .left | .right => typeNaming
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.BitwiseOr.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.BitwiseOr.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_1]
      unfold Modules.BitwiseOr.bitModuleStructure Contracts.Cycle.Certification.moduleStructure
      exact .composite ⟨"bitwise_or", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean.Naming.Primitive.or)
  | .vector length element, typeNaming => by
      rw [Modules.BitwiseOr.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_2]
      let splitter : Composition.SignalSplitter := .vector length element
      exact .composite ⟨"bitwise_or", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .left => "split_left"
          | .splitter .right => "split_right"
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .result => "combine")
        (fun
          | .splitter .left => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .splitter .right => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component => namingWith element (typeNaming.component component)
          | .combiner .result => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.BitwiseOr.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_3]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"bitwise_or", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .left => "split_left"
          | .splitter .right => "split_right"
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .result => "combine")
        (fun
          | .splitter .left => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .splitter .right => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .combiner .result => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.BitwiseOr.Naming
