import Silean2.CertifiedSchedule
import Silean2.Primitives.Or
import Silean2.SignalLogic

namespace Silean2.Modules.BitwiseOr

open Silean2

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .left | .right => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .result => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

inductive Rule | apply
deriving Enumeration

def outputRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((inputMap signalType).select .right).prepend .left
  writesOutputs := (outputMap signalType).select .result
  target | (left, (right, ())), _ => (signalType.bitwiseOr left right, ())

@[reducible] def cycleContract (signalType : SignalType) :
    ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

/-! The bit specialization is a readable wrapper around the closed OR
primitive. -/

inductive BitInstance | gate
deriving Enumeration

@[reducible] def bitInstances : Instances :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.or.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instances := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instances where
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  instanceInput
    | .gate, .left => bitContext.moduleInput .left
    | .gate, .right => bitContext.moduleInput .right

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildren : Certified.Children bitBody
  | .gate => Primitives.orCertified

def bitModuleStructure : ModuleStructure (ports .bit) :=
  Certified.moduleStructure bitBody bitChildren

abbrev bitRule : Certified.RuleOccurrence bitChildren :=
  ⟨.gate, Primitives.OrRule.apply⟩

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
      exact ⟨Primitives.OrRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Certified.StateSchedule bitBody bitChildren := .done trivial

def bitRuleSchedules : Certified.RuleSchedules bitBody bitChildren
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.OrRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs bitRuleSchedules .apply
  change bitRule ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule, Certified.Schedule.finalAvailability]

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
      ProposedValues (Certified.childStructure bitChildren name)
    | .gate => gate
  let outputs : (ports .bit).outputs.Values := fun
    | .result => gate.outputs .output
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child
    change Primitives.orCertified.moduleStructure.IsSolution
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
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [show (outputRule .bit).Holds inputs contractState proposal.outputs ↔
        proposal.outputs .result = (inputs .left || inputs .right) by
      simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
        SignalSelection.project, SignalSelection.prepend, SignalMap.select,
        SignalType.bitwiseOr]]
    rcases proposal with ⟨outputs, children⟩
    rcases satisfies with ⟨boundary, childSatisfies⟩
    change outputs .result = (inputs .left || inputs .right)
    have gate := childSatisfies .gate
    have boundaryResult := boundary .result
    change outputs .result = (children .gate).outputs .output at boundaryResult
    have gateInputs : ProposedValues.childInputs bitBody
        (Certified.childStructure bitChildren) inputs children .gate =
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

/-! Aggregate bitwise OR splits both operands, recursively ORs corresponding
components, then combines the results. -/

abbrev AggregateInstance (splitter : SignalSplitter) :=
  Enumeration.Framed (Sum PUnit splitter.ports.outputs.Label)

@[reducible] def aggregateInstances (splitter : SignalSplitter) : Instances where
  Key := AggregateInstance splitter
  keys := Enumeration.framed
    (Enumeration.sum Enumeration.punit splitter.ports.outputs.labels)
  value
    | .start => splitter.ports
    | .item (.inl _) => splitter.ports
    | .item (.inr component) =>
        ports (splitter.ports.outputs.signalType component)
    | .finish => splitter.combiner.ports

@[reducible] def aggregateContext (splitter : SignalSplitter) : EndpointContext where
  ports := ports splitter.aggregateType
  instances := aggregateInstances splitter

def aggregateWiring (splitter : SignalSplitter) :
    Wiring (aggregateContext splitter).ports (aggregateContext splitter).instances :=
  match splitter with
  | .vector length element => {
      moduleOutput := fun port => match port with
        | .result => (aggregateContext (.vector length element)).instanceOutput
            .finish AggregatePort.value
      instanceInput := fun
        | .start, AggregatePort.value =>
            (aggregateContext (.vector length element)).moduleInput .left
        | .item (.inl _), AggregatePort.value =>
            (aggregateContext (.vector length element)).moduleInput .right
        | .item (.inr component), .left =>
            (aggregateContext (.vector length element)).instanceOutput .start component
        | .item (.inr component), .right =>
            (aggregateContext (.vector length element)).instanceOutput
              (.item (.inl .unit)) component
        | .finish, component =>
            (aggregateContext (.vector length element)).instanceOutput
              (.item (.inr component)) .result }
  | .tuple fields => {
      moduleOutput := fun port => match port with
        | .result => (aggregateContext (.tuple fields)).instanceOutput
            .finish AggregatePort.value
      instanceInput := fun
        | .start, AggregatePort.value =>
            (aggregateContext (.tuple fields)).moduleInput .left
        | .item (.inl _), AggregatePort.value =>
            (aggregateContext (.tuple fields)).moduleInput .right
        | .item (.inr component), .left =>
            (aggregateContext (.tuple fields)).instanceOutput .start component
        | .item (.inr component), .right =>
            (aggregateContext (.tuple fields)).instanceOutput
              (.item (.inl .unit)) component
        | .finish, component =>
            (aggregateContext (.tuple fields)).instanceOutput
              (.item (.inr component)) .result }

@[reducible] def aggregateBody (splitter : SignalSplitter) : ModuleBody :=
  ⟨aggregateContext splitter, aggregateWiring splitter⟩

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  | .bit => bitModuleStructure
  | .vector length element =>
      .composite (aggregateBody (.vector length element)) fun
        | .start => .splitter (.vector length element)
        | .item (.inl _) => .splitter (.vector length element)
        | .item (.inr _) => moduleStructure element
        | .finish => .combiner (.vector length element)
  | .tuple fields =>
      .composite (aggregateBody (.tuple fields)) fun
        | .start => .splitter (.tuple fields)
        | .item (.inl _) => .splitter (.tuple fields)
        | .item (.inr component) => moduleStructure (fields.typeAt component)
        | .finish => .combiner (.tuple fields)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

structure Implementation (signalType : SignalType) where
  moduleStructure : ModuleStructure (ports signalType)
  moduleStructure_eq : moduleStructure = BitwiseOr.moduleStructure signalType
  hasStructuralResult : ∀ inputs state,
    ∃ proposal, moduleStructure.IsSolution inputs state proposal
  structuralResultUnique : moduleStructure.HasAtMostOneSolution
  implements : Implements moduleStructure (cycleContract signalType)
    (fun _ _ => True)

def Implementation.certified (implementation : Implementation signalType) :
    ModuleCycleCertified (ports signalType) where
  moduleStructure := implementation.moduleStructure
  cycleContract := cycleContract signalType
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := implementation.hasStructuralResult
  structuralResultUnique := implementation.structuralResultUnique
  implements := implementation.implements

def bitImplementation : Implementation .bit where
  moduleStructure := bitModuleStructure
  moduleStructure_eq := by unfold moduleStructure; rfl
  hasStructuralResult := bitHasStructuralResult
  structuralResultUnique := bitHasAtMostOneSolution
  implements := bitImplements

@[reducible] def aggregateChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.Children (aggregateBody splitter)
  | .start => splitter.certified
  | .item (.inl _) => splitter.certified
  | .item (.inr component) => (components component).certified
  | .finish => splitter.combiner.certified

@[reducible] def aggregateChildStructure (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :=
  Certified.childStructure (aggregateChildren splitter components)

def leftSplitterInputs (splitter : SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .left)

def rightSplitterInputs (splitter : SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .right)

def componentInputs (splitter : SignalSplitter)
    (leftSplit rightSplit : ProposedValues splitter.certified.moduleStructure)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values
  | .left => leftSplit.outputs component
  | .right => rightSplit.outputs component

def combinerInputs (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (proposals : (component : splitter.ports.outputs.Label) →
      ProposedValues (components component).moduleStructure) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter <;> exact fun component => (proposals component).outputs .result

def aggregateOutputs (splitter : SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .result => combineProposal.outputs .value
  | .tuple _ => fun | .result => combineProposal.outputs .value

theorem aggregateHasStructuralResult (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (state : (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).IsSolution inputs state proposal := by
  rcases splitter.certified.hasStructuralResult
      (leftSplitterInputs splitter inputs) (state .start) with
    ⟨leftSplit, leftSplitSatisfies⟩
  rcases splitter.certified.hasStructuralResult
      (rightSplitterInputs splitter inputs) (state (.item (.inl .unit))) with
    ⟨rightSplit, rightSplitSatisfies⟩
  let Property := fun component proposal =>
    (components component).moduleStructure.IsSolution
      (componentInputs splitter leftSplit rightSplit component)
      (state (.item (.inr component))) proposal
  have available : ∀ component, ∃ proposal, Property component proposal :=
    fun component => (components component).hasStructuralResult _ _
  rcases splitter.ports.outputs.labels.exists_pi Property available with
    ⟨componentProposals, componentSatisfies⟩
  rcases splitter.combiner.certified.hasStructuralResult
      (combinerInputs splitter components componentProposals) (state .finish) with
    ⟨combineProposal, combineSatisfies⟩
  let children : (name : AggregateInstance splitter) →
      ProposedValues (aggregateChildStructure splitter components name)
    | .start => leftSplit
    | .item (.inl _) => rightSplit
    | .item (.inr component) => componentProposals component
    | .finish => combineProposal
  refine ⟨ProposedValues.composite (aggregateOutputs splitter combineProposal)
    children, ?_⟩
  constructor
  · intro output; cases output; cases splitter <;> rfl
  · intro child
    cases child with
    | start =>
        change splitter.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs children .start)
          (state .start) leftSplit
        rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs children .start =
            leftSplitterInputs splitter inputs by
          cases splitter <;> funext port <;> cases port <;> rfl]
        exact leftSplitSatisfies
    | item role =>
        cases role with
        | inl singleton =>
            cases singleton
            change splitter.certified.moduleStructure.IsSolution
              (ProposedValues.childInputs (aggregateBody splitter)
                (aggregateChildStructure splitter components) inputs children
                  (.item (.inl .unit)))
              (state (.item (.inl .unit))) rightSplit
            rw [show ProposedValues.childInputs (aggregateBody splitter)
              (aggregateChildStructure splitter components) inputs children
                (.item (.inl .unit)) = rightSplitterInputs splitter inputs by
              cases splitter <;> funext port <;> cases port <;> rfl]
            exact rightSplitSatisfies
        | inr component =>
            change (components component).moduleStructure.IsSolution
              (ProposedValues.childInputs (aggregateBody splitter)
                (aggregateChildStructure splitter components) inputs children
                  (.item (.inr component)))
              (state (.item (.inr component))) (componentProposals component)
            rw [show ProposedValues.childInputs (aggregateBody splitter)
              (aggregateChildStructure splitter components) inputs children
                (.item (.inr component)) =
                  componentInputs splitter leftSplit rightSplit component by
              cases splitter <;> funext port <;> cases port <;> rfl]
            exact componentSatisfies component
    | finish =>
        change splitter.combiner.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs children .finish)
          (state .finish) combineProposal
        rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs children .finish =
            combinerInputs splitter components componentProposals by
          cases splitter <;> funext port <;> rfl]
        exact combineSatisfies

abbrev leftSplitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.start, SignalComponentRule.apply⟩

abbrev rightSplitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.item (.inl .unit), SignalComponentRule.apply⟩

abbrev componentOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.item (.inr component), Rule.apply⟩

abbrev combineOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.finish, SignalComponentRule.apply⟩

@[simp] theorem leftSplitOccurrence_writes (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (leftSplitOccurrence splitter components).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

@[simp] theorem rightSplitOccurrence_writes (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (rightSplitOccurrence splitter components).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

theorem componentOccurrence_injective (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Function.Injective (componentOccurrence splitter components) := by
  intro left right equal
  have childEqual : Enumeration.Framed.item (Sum.inr left) =
      Enumeration.Framed.item (Sum.inr right) :=
    congrArg Certified.RuleOccurrence.child equal
  exact Sum.inr.inj (Enumeration.Framed.item.inj childEqual)

noncomputable def componentSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.Schedule (aggregateBody splitter)
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
  Certified.Schedule.callFamilyAfter
    ([rightSplitOccurrence splitter components,
      leftSplitOccurrence splitter components] : Certified.Availability
      (aggregateChildren splitter components))
    splitter.ports.outputs.labels (componentOccurrence splitter components)
    (componentOccurrence_injective splitter components)
    (by
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro component input member
      cases input with
      | left =>
          cases splitter with
          | vector length element =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (leftSplitOccurrence (.vector length element) components).writes
                  rw [leftSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (leftSplitOccurrence (.tuple fields) components).writes
                  rw [leftSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
      | right =>
          cases splitter with
          | vector length element =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (rightSplitOccurrence (.vector length element) components).writes
                  rw [rightSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨SignalComponentRule.apply, by simp,
                by
                  change component ∈
                    (rightSplitOccurrence (.tuple fields) components).writes
                  rw [rightSplitOccurrence_writes]
                  exact ListIndex.get_eq
                    ((SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                      List.get_mem _ _⟩)

theorem aggregateBoundaryReady (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
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

noncomputable def aggregateAfterSplitsSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Certified.BoundaryReady (aggregateBody splitter)
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
        have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
        cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      cases equal
  · exact aggregateBoundaryReady splitter components (by simp)

noncomputable def aggregateOutputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .apply := by
  refine .call (leftSplitOccurrence splitter components) ?_ (by simp) ?_
  · intro input member
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
        aggregateWiring, aggregateContext, EndpointContext.moduleInput]
  · refine .call (rightSplitOccurrence splitter components) ?_ (by simp) ?_
    · intro input member
      cases splitter <;> cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
          aggregateWiring, aggregateContext, EndpointContext.moduleInput]
    · exact aggregateAfterSplitsSchedule splitter components

def aggregateStateSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) := .done trivial

noncomputable def aggregateRuleSchedules (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType) where
  output | .apply => aggregateOutputSchedule splitter components
  state := aggregateStateSchedule splitter components

theorem leftSplit_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    leftSplitOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change leftSplitOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.1 _ (by simp))

theorem rightSplit_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    rightSplitOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change rightSplitOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.1 _ (by simp))

theorem component_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter components component ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change componentOccurrence splitter components component ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.2.1 component)

theorem combine_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    combineOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change combineOccurrence splitter components ∈
    (aggregateAfterSplitsSchedule splitter components).finalAvailability
  unfold aggregateAfterSplitsSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_self

theorem aggregateCoversChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (aggregateRuleSchedules splitter components).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (aggregateRuleSchedules splitter components) .apply
  cases child with
  | start =>
      change SignalComponentRule at rule
      cases rule
      exact leftSplit_mem_outputSchedule splitter components
  | item role =>
      cases role with
      | inl singleton =>
          cases singleton
          change SignalComponentRule at rule
          cases rule
          exact rightSplit_mem_outputSchedule splitter components
      | inr component =>
          change Rule at rule
          cases rule
          exact component_mem_outputSchedule splitter components component
  | finish =>
      change SignalComponentRule at rule
      cases rule
      exact combine_mem_outputSchedule splitter components

theorem aggregateHasAtMostOneSolution (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).HasAtMostOneSolution :=
  (aggregateRuleSchedules splitter components).hasAtMostOneSolution
    (aggregateCoversChildren splitter components)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.bitwiseOr (inputs .left) (inputs .right) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

private theorem aggregateImplements (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implements
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have leftSplitOutputs : (childProposals .start).outputs =
      splitter.outputValues (leftSplitterInputs splitter inputs) := by
    cases splitter <;> exact childSatisfies .start
  have rightSplitOutputs :
      (childProposals (.item (.inl .unit))).outputs =
        splitter.outputValues (rightSplitterInputs splitter inputs) := by
    cases splitter <;> exact childSatisfies (.item (.inl .unit))
  have componentOutputs : ∀ component,
      (childProposals (.item (.inr component))).outputs .result =
        (splitter.ports.outputs.signalType component).bitwiseOr
          (splitter.outputValues (leftSplitterInputs splitter inputs) component)
          (splitter.outputValues (rightSplitterInputs splitter inputs) component) := by
    intro component
    rcases (components component).implements
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.item (.inr component)))
        SignalMap.emptyValues (structuralState (.item (.inr component)))
        (childProposals (.item (.inr component))) trivial
        (childSatisfies (.item (.inr component))) with
      ⟨nextState, evaluates, nextCorresponds⟩
    have holds := evaluates.1 Rule.apply
    rw [outputRule_holds_iff] at holds
    have leftInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.item (.inr component))) .left =
      splitter.outputValues (leftSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (.item (.inr component))) .right =
      splitter.outputValues (rightSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact holds.trans (by rw [leftInput, rightInput])
  have combineOutputs : (childProposals .finish).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          .finish) := by cases splitter <;> exact childSatisfies .finish
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
          (childProposals .finish).outputs AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs AggregatePort.value]
        change (fun component =>
          (childProposals (.item (.inr component))).outputs .result) = _
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals .finish).outputs AggregatePort.value at boundaryResult
        rw [boundaryResult]
        rw [congrFun combineOutputs AggregatePort.value]
        change fields.assemble (fun component =>
          (childProposals (.item (.inr component))).outputs .result) =
            fields.bitwiseOr (inputs .left) (inputs .right)
        rw [← fields.assemble_get (fields.bitwiseOr (inputs .left) (inputs .right))]
        apply congrArg fields.assemble
        funext component
        exact (componentOutputs component).trans
          (fields.get_bitwiseOr (inputs .left) (inputs .right) component).symm
  · rfl

noncomputable def aggregateImplementation (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implementation splitter.aggregateType where
  moduleStructure := Certified.moduleStructure (aggregateBody splitter)
    (aggregateChildren splitter components)
  moduleStructure_eq := by
    cases splitter with
    | vector length element =>
        unfold Certified.moduleStructure Certified.childStructure aggregateChildren
          moduleStructure
        change ModuleStructure.composite _ _ = ModuleStructure.composite _ _
        congr 1
        funext child
        cases child with
        | start => rfl
        | item role =>
            cases role with
            | inl singleton => cases singleton; rfl
            | inr component => exact (components component).moduleStructure_eq
        | finish => rfl
    | tuple fields =>
        unfold Certified.moduleStructure Certified.childStructure aggregateChildren
          moduleStructure
        change ModuleStructure.composite _ _ = ModuleStructure.composite _ _
        congr 1
        funext child
        cases child with
        | start => rfl
        | item role =>
            cases role with
            | inl singleton => cases singleton; rfl
            | inr component => exact (components component).moduleStructure_eq
        | finish => rfl
  hasStructuralResult := aggregateHasStructuralResult splitter components
  structuralResultUnique := aggregateHasAtMostOneSolution splitter components
  implements := aggregateImplements splitter components

noncomputable def implementation : (signalType : SignalType) → Implementation signalType
  | .bit => bitImplementation
  | .vector length element =>
      aggregateImplementation (.vector length element) fun _ => implementation element
  | .tuple fields =>
      aggregateImplementation (.tuple fields) fun component =>
        implementation (fields.typeAt component)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) := (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  (implementation signalType).moduleStructure_eq

end Silean2.Modules.BitwiseOr
