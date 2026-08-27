import Silean2.CertifiedSchedule
import Silean2.Modules.All
import Silean2.Naming.PrimitiveNaming
import Silean2.Naming.SignalAdapterNaming
import Silean2.Primitives.Eq
import Silean2.SignalLogic

namespace Silean2.Modules.Equality

open Silean2

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun | .left | .right => signalType

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .result => .bit

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap⟩

inductive Rule | apply
deriving Enumeration

def outputRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons .bit .nil } where
  readsInputs := ((inputMap signalType).select .right).prepend .left
  writesOutputs := outputMap.select .result
  target | (left, (right, ())), _ => (signalType.equal left right, ())

@[reducible] def cycleContract (signalType : SignalType) :
    ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.equal (inputs .left) (inputs .right) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem output_eq_true_iff_of_holds (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (holds : (outputRule signalType).Holds inputs state outputs) :
    outputs .result = true ↔ inputs .left = inputs .right := by
  rw [(outputRule_holds_iff signalType inputs state outputs).mp holds]
  exact signalType.equal_eq_true_iff _ _

/-! The bit case is a transparent wrapper around the closed equality
primitive. -/

inductive BitInstance | gate
deriving Enumeration

@[reducible] def bitInstances : Instances :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.eq.ports

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
  | .gate => Primitives.eqCertified

def bitModuleStructure : ModuleStructure (ports .bit) :=
  Certified.moduleStructure bitBody bitChildren

abbrev bitOccurrence : Certified.RuleOccurrence bitChildren :=
  ⟨.gate, Primitives.EqRule.apply⟩

def bitOutputSchedule : Certified.OutputSchedule bitBody bitChildren
    (cycleContract .bit) .apply :=
  .call bitOccurrence
    (by
      intro input member
      cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
          bitBody, bitWiring, bitContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output _
      cases output
      exact ⟨Primitives.EqRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Certified.StateSchedule bitBody bitChildren :=
  .done (by
    intro child input member
    cases child
    simp [bitChildren, Primitives.eqCertified, Primitives.eqCycleContract,
      CycleStateRule.empty, SignalSelection.labels] at member)

def bitRuleSchedules : Certified.RuleSchedules bitBody bitChildren
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.EqRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs bitRuleSchedules .apply
  change bitOccurrence ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule, Certified.Schedule.finalAvailability]

theorem bitHasAtMostOneSolution : bitModuleStructure.HasAtMostOneSolution :=
  bitRuleSchedules.hasAtMostOneSolution bitCoversChildren

def bitGateInputs (inputs : (ports .bit).inputs.Values) :
    Primitives.eq.ports.inputs.Values
  | .left => inputs .left
  | .right => inputs .right

theorem bitHasStructuralResult (inputs : (ports .bit).inputs.Values)
    (state : bitModuleStructure.State) :
    ∃ proposal, bitModuleStructure.IsSolution inputs state proposal := by
  rcases Primitives.eqCertified.hasStructuralResult
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
    change Primitives.eqCertified.moduleStructure.IsSolution
      (ProposedValues.childInputs bitBody (Certified.childStructure bitChildren)
        inputs children .gate) (state .gate) gate
    rw [show ProposedValues.childInputs bitBody
      (Certified.childStructure bitChildren) inputs children .gate =
        bitGateInputs inputs by funext port; cases port <;> rfl]
    exact gateSatisfies

private theorem bitImplements : Implements bitModuleStructure
    (cycleContract .bit) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    have gateSatisfies := childSatisfies .gate
    have gateInputs : ProposedValues.childInputs bitBody
        (Certified.childStructure bitChildren) inputs children .gate =
          bitGateInputs inputs := by funext port; cases port <;> rfl
    have gateEquation := gateSatisfies.1
    rw [gateInputs] at gateEquation
    exact (boundary .result).trans ((congrFun gateEquation .output).trans (by
      simp [Primitives.eq, SignalType.equal, bitGateInputs]))
  · rfl

def bitCertification : ModuleCycleCertification bitModuleStructure
    (cycleContract .bit) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := bitHasStructuralResult
  structuralResultUnique := bitHasAtMostOneSolution
  implements := bitImplements

/-! Aggregate equality has two splitters, one recursive equality child per
immediate component, and one `All` child consuming the family of results. -/

abbrev AggregateInstance (splitter : SignalSplitter) :=
  Sum Input (Sum splitter.ports.outputs.Label PUnit)

@[reducible] def aggregateInstanceEnumeration (splitter : SignalSplitter) :
    Enumeration (AggregateInstance splitter) :=
  Enumeration.sum inferInstance
    (Enumeration.sum splitter.ports.outputs.labels Enumeration.punit)

private abbrev splitInstance (input : Input) : AggregateInstance splitter := .inl input
private abbrev componentInstance (component : splitter.ports.outputs.Label) :
    AggregateInstance splitter := .inr (.inl component)
private abbrev allInstance : AggregateInstance splitter := .inr (.inr .unit)

def componentCount (splitter : SignalSplitter) : Nat :=
  splitter.ports.outputs.labels.values.length

@[reducible] def aggregateInstances (splitter : SignalSplitter) : Instances where
  Key := AggregateInstance splitter
  keys := aggregateInstanceEnumeration splitter
  value
    | .inl _ => splitter.ports
    | .inr (.inl component) =>
        ports (splitter.ports.outputs.signalType component)
    | .inr (.inr _) => All.ports (componentCount splitter)

@[reducible] def aggregateContext (splitter : SignalSplitter) : EndpointContext where
  ports := ports splitter.aggregateType
  instances := aggregateInstances splitter

private def componentAt (splitter : SignalSplitter)
    (index : Fin (componentCount splitter)) : splitter.ports.outputs.Label :=
  splitter.ports.outputs.labels.values[index.val]'(by
    simp [componentCount])

@[simp] theorem componentAt_ordinal (splitter : SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    componentAt splitter (splitter.ports.outputs.labels.ordinal component) =
      component := by
  exact (splitter.ports.outputs.labels.locate component).get_eq

theorem all_components_equal_iff (splitter : SignalSplitter)
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

def aggregateWiring (splitter : SignalSplitter) :
    Wiring (aggregateContext splitter).ports (aggregateContext splitter).instances where
  moduleOutput
    | .result => (aggregateContext splitter).instanceOutput allInstance .output
  instanceInput
    | .inl input, aggregateInput => by
        cases splitter with
        | vector length element =>
            cases aggregateInput
            cases input with
            | left => exact (aggregateContext (.vector length element)).moduleInput .left
            | right => exact (aggregateContext (.vector length element)).moduleInput .right
        | tuple fields =>
            cases aggregateInput
            cases input with
            | left => exact (aggregateContext (.tuple fields)).moduleInput .left
            | right => exact (aggregateContext (.tuple fields)).moduleInput .right
    | .inr (.inl component), .left =>
        (aggregateContext splitter).instanceOutput (splitInstance .left) component
    | .inr (.inl component), .right =>
        (aggregateContext splitter).instanceOutput (splitInstance .right) component
    | .inr (.inr _), input =>
        (aggregateContext splitter).instanceOutput
          (componentInstance (componentAt splitter
            (All.inputIndex (componentCount splitter) input))) .result

@[reducible] def aggregateBody (splitter : SignalSplitter) : ModuleBody :=
  ⟨aggregateContext splitter, aggregateWiring splitter⟩

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  | .bit => bitModuleStructure
  | .vector length element =>
      .composite (aggregateBody (.vector length element)) fun
        | .inl _ => .splitter (.vector length element)
        | .inr (.inl _) => moduleStructure element
        | .inr (.inr _) =>
            All.moduleStructure (componentCount (.vector length element))
  | .tuple fields =>
      .composite (aggregateBody (.tuple fields)) fun
        | .inl _ => .splitter (.tuple fields)
        | .inr (.inl component) => moduleStructure (fields.typeAt component)
        | .inr (.inr _) =>
            All.moduleStructure (componentCount (.tuple fields))
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

abbrev Implementation (signalType : SignalType) :=
  ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

def Implementation.certified (implementation : Implementation signalType) :
    ModuleCycleCertified (ports signalType) := implementation.bundle

@[reducible] def aggregateChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.Children (aggregateBody splitter)
  | .inl _ => splitter.certified
  | .inr (.inl component) => (components component).certified
  | .inr (.inr _) => All.certified (componentCount splitter)

@[reducible] def aggregateChildStructure (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :=
  Certified.childStructure (aggregateChildren splitter components)

theorem aggregateModuleStructure_eq (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    moduleStructure splitter.aggregateType =
      Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components) := by
  cases splitter with
  | vector length element =>
      simp only [SignalSplitter.aggregateType, moduleStructure,
        Certified.moduleStructure]
      congr
      funext child
      rcases child with input | componentOrAll
      · cases input <;> rfl
      · rcases componentOrAll with component | allTag
        · rfl
        · cases allTag; rfl
  | tuple fields =>
      simp only [SignalSplitter.aggregateType, moduleStructure,
        Certified.moduleStructure]
      congr
      funext child
      rcases child with input | componentOrAll
      · cases input <;> rfl
      · rcases componentOrAll with component | allTag
        · rfl
        · cases allTag; rfl

def splitterInputs (splitter : SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) (which : Input) :
    splitter.ports.inputs.Values := match which with
  | .left => splitter.inputValues (inputs .left)
  | .right => splitter.inputValues (inputs .right)

def componentInputs (splitter : SignalSplitter)
    (leftSplit rightSplit : ProposedValues splitter.certified.moduleStructure)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values
  | .left => leftSplit.outputs component
  | .right => rightSplit.outputs component

def allInputs (splitter : SignalSplitter)
    (componentProposals : (component : splitter.ports.outputs.Label) →
      ProposedValues (moduleStructure
        (splitter.ports.outputs.signalType component))) :
    (All.ports (componentCount splitter)).inputs.Values := fun input =>
  (componentProposals
    (componentAt splitter (All.inputIndex (componentCount splitter) input))).outputs .result

private def aggregateChildProposals (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (leftSplit rightSplit : ProposedValues splitter.certified.moduleStructure)
    (componentProposals : (component : splitter.ports.outputs.Label) →
      ProposedValues (moduleStructure
        (splitter.ports.outputs.signalType component)))
    (allProposal : ProposedValues (All.moduleStructure (componentCount splitter))) :
    (child : AggregateInstance splitter) →
      ProposedValues (aggregateChildStructure splitter components child)
  | .inl .left => leftSplit
  | .inl .right => rightSplit
  | .inr (.inl component) => componentProposals component
  | .inr (.inr _) => allProposal

theorem aggregateHasStructuralResult (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (state : (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).State) :
    ∃ proposal, (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).IsSolution inputs state proposal := by
  rcases splitter.certified.hasStructuralResult
      (splitterInputs splitter inputs .left) (state (splitInstance .left)) with
    ⟨leftSplit, leftSatisfies⟩
  rcases splitter.certified.hasStructuralResult
      (splitterInputs splitter inputs .right) (state (splitInstance .right)) with
    ⟨rightSplit, rightSatisfies⟩
  let Property := fun component proposal =>
    (components component).certified.moduleStructure.IsSolution
      (componentInputs splitter leftSplit rightSplit component)
      (state (componentInstance component)) proposal
  have componentExists : ∀ component, ∃ proposal, Property component proposal := by
    intro component
    exact (components component).hasStructuralResult
      (componentInputs splitter leftSplit rightSplit component)
      (state (componentInstance component))
  rcases splitter.ports.outputs.labels.exists_pi Property componentExists with
    ⟨componentProposals, componentsSatisfy⟩
  rcases (All.certified (componentCount splitter)).hasStructuralResult
      (allInputs splitter componentProposals) (state allInstance) with
    ⟨allProposal, allSatisfies⟩
  let childProposals := aggregateChildProposals splitter components leftSplit
    rightSplit componentProposals allProposal
  let outputs : (ports splitter.aggregateType).outputs.Values := fun
    | .result => allProposal.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    rcases child with input | componentOrAll
    · cases input with
      | left =>
          change splitter.certified.moduleStructure.IsSolution
            (ProposedValues.childInputs (aggregateBody splitter) _ inputs
              childProposals (splitInstance .left))
            (state (splitInstance .left)) leftSplit
          rw [show ProposedValues.childInputs (aggregateBody splitter) _ inputs
              childProposals (splitInstance .left) =
                splitterInputs splitter inputs .left by
            cases splitter <;> funext port <;> cases port <;>
              change inputs .left = inputs .left <;> rfl]
          exact leftSatisfies
      | right =>
          change splitter.certified.moduleStructure.IsSolution
            (ProposedValues.childInputs (aggregateBody splitter) _ inputs
              childProposals (splitInstance .right))
            (state (splitInstance .right)) rightSplit
          rw [show ProposedValues.childInputs (aggregateBody splitter) _ inputs
              childProposals (splitInstance .right) =
                splitterInputs splitter inputs .right by
            cases splitter <;> funext port <;> cases port <;>
              change inputs .right = inputs .right <;> rfl]
          exact rightSatisfies
    · rcases componentOrAll with component | allTag
      · change (components component).certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter) _ inputs
            childProposals (componentInstance component))
          (state (componentInstance component)) (componentProposals component)
        rw [show ProposedValues.childInputs (aggregateBody splitter) _ inputs
            childProposals (componentInstance component) =
              componentInputs splitter leftSplit rightSplit component by
          cases splitter <;> funext port <;> cases port <;> rfl]
        exact componentsSatisfy component
      · cases allTag
        change (All.certified (componentCount splitter)).moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter) _ inputs
            childProposals allInstance) (state allInstance) allProposal
        rw [show ProposedValues.childInputs (aggregateBody splitter) _ inputs
            childProposals allInstance = allInputs splitter componentProposals by
          funext input
          rfl]
        exact allSatisfies

abbrev leftSplitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨splitInstance .left, SignalComponentRule.apply⟩

abbrev rightSplitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨splitInstance .right, SignalComponentRule.apply⟩

abbrev componentOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨componentInstance component, Rule.apply⟩

abbrev allOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨allInstance, All.Rule.apply⟩

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
    [rightSplitOccurrence splitter components,
      leftSplitOccurrence splitter components]
    splitter.ports.outputs.labels
    (componentOccurrence splitter components)
    (by
      intro left right equal
      have childEqual := congrArg Certified.RuleOccurrence.child equal
      exact Sum.inl.inj (Sum.inr.inj childEqual))
    (by
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro component input _
      cases input with
      | left =>
          refine ⟨SignalComponentRule.apply, by simp, ?_⟩
          change component ∈ (leftSplitOccurrence splitter components).writes
          rw [leftSplitOccurrence_writes]
          exact ListIndex.get_eq
            (splitter.ports.outputs.labels.locate component) ▸ List.get_mem _ _
      | right =>
          refine ⟨SignalComponentRule.apply, by simp, ?_⟩
          change component ∈ (rightSplitOccurrence splitter components).writes
          rw [rightSplitOccurrence_writes]
          exact ListIndex.get_eq
            (splitter.ports.outputs.labels.locate component) ▸ List.get_mem _ _)

noncomputable def afterComponentsSchedule (splitter : SignalSplitter)
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
  refine .call (allOccurrence splitter components) ?_ ?_ (.done ?_)
  · intro input _
    let component := componentAt splitter
      (All.inputIndex (componentCount splitter) input)
    refine ⟨Rule.apply,
      (componentSchedule splitter components).finished.2.1 component, ?_⟩
    change Output.result ∈
      (outputRule (splitter.ports.outputs.signalType component)).writesOutputs.labels
    simp [outputRule, SignalMap.select, SignalSelection.labels]
  · intro present
    rcases (componentSchedule splitter components).finished.2.2 _ present with
      atStart | fromComponent
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at atStart
      rcases atStart with equal | equal <;>
        have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
        cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      have childEqual := congrArg Certified.RuleOccurrence.child equal
      cases childEqual
  · intro output _
    cases output
    exact ⟨All.Rule.apply, by simp, by
      change Primitives.SingleOutput.output ∈
        (All.outputRule (componentCount splitter)).writesOutputs.labels
      simp [All.outputRule, SignalMap.select, SignalSelection.labels]⟩

noncomputable def aggregateOutputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .apply := by
  refine .call (leftSplitOccurrence splitter components) ?_ (by simp) ?_
  · intro input _
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
        aggregateWiring, aggregateContext, EndpointContext.moduleInput]
  · refine .call (rightSplitOccurrence splitter components) ?_
      (by
        intro member
        have equal := List.mem_singleton.mp member
        have childEqual := congrArg Certified.RuleOccurrence.child equal
        have inputEqual : Input.right = Input.left := by injection childEqual
        cases inputEqual) ?_
    · intro input _
      cases splitter <;> cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Certified.sourceAvailable, aggregateBody,
          aggregateWiring, aggregateContext, EndpointContext.moduleInput]
    · exact afterComponentsSchedule splitter components

def aggregateStateSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) :=
  .done (by
    intro child input member
    rcases child with which | componentOrAll
    · cases which <;>
        simp [aggregateChildren, SignalSplitter.certified,
          SignalSplitter.cycleContract, CycleStateRule.empty,
          SignalSelection.labels] at member
    · rcases componentOrAll with component | allTag
      · simp [aggregateChildren, Implementation.certified,
          ModuleCycleCertification.bundle, cycleContract,
          CycleStateRule.empty, SignalSelection.labels] at member
      · cases allTag
        rw [show (aggregateChildren splitter components allInstance).cycleContract =
            All.cycleContract (componentCount splitter) by rfl] at member
        change input ∈ SignalSelection.nil.labels at member
        exact nomatch member)

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
    (afterComponentsSchedule splitter components).finalAvailability
  unfold afterComponentsSchedule
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
    (afterComponentsSchedule splitter components).finalAvailability
  unfold afterComponentsSchedule
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
    (afterComponentsSchedule splitter components).finalAvailability
  unfold afterComponentsSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter components).finished.2.1 component)

theorem all_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    allOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  unfold aggregateOutputSchedule
  change allOccurrence splitter components ∈
    (afterComponentsSchedule splitter components).finalAvailability
  unfold afterComponentsSchedule
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
  rcases child with which | componentOrAll
  · cases which with
    | left =>
        change SignalComponentRule at rule
        cases rule
        exact leftSplit_mem_outputSchedule splitter components
    | right =>
        change SignalComponentRule at rule
        cases rule
        exact rightSplit_mem_outputSchedule splitter components
  · rcases componentOrAll with component | allTag
    · change Rule at rule
      cases rule
      exact component_mem_outputSchedule splitter components component
    · cases allTag
      change All.Rule at rule
      cases rule
      exact all_mem_outputSchedule splitter components

theorem aggregateHasAtMostOneSolution (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter components)).HasAtMostOneSolution :=
  (aggregateRuleSchedules splitter components).hasAtMostOneSolution
    (aggregateCoversChildren splitter components)

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
  have leftSplitOutputs : (childProposals (splitInstance .left)).outputs =
      splitter.outputValues (splitterInputs splitter inputs .left) := by
    cases splitter <;> exact childSatisfies (splitInstance .left)
  have rightSplitOutputs : (childProposals (splitInstance .right)).outputs =
      splitter.outputValues (splitterInputs splitter inputs .right) := by
    cases splitter <;> exact childSatisfies (splitInstance .right)
  have componentOutputs : ∀ component,
      (childProposals (componentInstance component)).outputs .result =
        (splitter.ports.outputs.signalType component).equal
          (splitter.outputValues (splitterInputs splitter inputs .left) component)
          (splitter.outputValues (splitterInputs splitter inputs .right) component) := by
    intro component
    rcases (components component).hasCorrespondingState
        (structuralState (componentInstance component)) with
      ⟨componentState, componentCorresponds⟩
    have componentState_eq : componentState = SignalMap.emptyValues := by
      funext impossible
      exact nomatch impossible
    subst componentState
    rcases (components component).implements
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (componentInstance component))
        SignalMap.emptyValues (structuralState (componentInstance component))
        (childProposals (componentInstance component)) componentCorresponds
        (childSatisfies (componentInstance component)) with
      ⟨nextState, evaluates, nextCorresponds⟩
    have equation := evaluates.1 Rule.apply
    rw [outputRule_holds_iff] at equation
    have leftInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (componentInstance component)) .left =
        splitter.outputValues (splitterInputs splitter inputs .left) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
          (componentInstance component)) .right =
        splitter.outputValues (splitterInputs splitter inputs .right) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact equation.trans (by rw [leftInput, rightInput])
  rcases (All.certified (componentCount splitter)).hasCorrespondingState
      (structuralState allInstance) with ⟨allState, allCorresponds⟩
  have allState_eq : allState = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  subst allState
  rcases (All.certified (componentCount splitter)).implements
      (ProposedValues.childInputs (aggregateBody splitter)
        (aggregateChildStructure splitter components) inputs childProposals allInstance)
      SignalMap.emptyValues (structuralState allInstance)
      (childProposals allInstance) allCorresponds (childSatisfies allInstance) with
    ⟨nextAllState, allEvaluates, nextAllCorresponds⟩
  have allHolds := allEvaluates.1 All.Rule.apply
  change (All.outputRule (componentCount splitter)).Holds
    (ProposedValues.childInputs (aggregateBody splitter)
      (aggregateChildStructure splitter components) inputs childProposals allInstance)
    SignalMap.emptyValues (childProposals allInstance).outputs at allHolds
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = splitter.aggregateType.equal
      (inputs .left) (inputs .right)
    apply Bool.eq_iff_iff.mpr
    rw [show outputs .result = (childProposals allInstance).outputs .output by
      exact boundary .result]
    have allCharacterization := All.output_eq_true_iff_of_holds
      (componentCount splitter)
      (ProposedValues.childInputs (aggregateBody splitter)
        (aggregateChildStructure splitter components) inputs childProposals allInstance)
      SignalMap.emptyValues (childProposals allInstance).outputs allHolds
    refine allCharacterization.trans ?_
    rw [splitter.aggregateType.equal_eq_true_iff]
    rw [← all_components_equal_iff splitter]
    constructor
    · intro every component
      have result := every (splitter.ports.outputs.labels.ordinal component)
      rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals allInstance
          (All.input (componentCount splitter)
            (splitter.ports.outputs.labels.ordinal component)) =
          (childProposals (componentInstance component)).outputs .result by
        simp [ProposedValues.childInputs, aggregateBody, aggregateWiring,
          EndpointContext.instanceOutput, SignalSource.value]
        rw [All.inputIndex_input, componentAt_ordinal]] at result
      rw [componentOutputs component] at result
      exact ((splitter.ports.outputs.signalType component).equal_eq_true_iff _ _).mp result
    · intro every index
      let component := componentAt splitter index
      rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals allInstance
          (All.input (componentCount splitter) index) =
          (childProposals (componentInstance component)).outputs .result by
        simp [ProposedValues.childInputs, aggregateBody, aggregateWiring,
          EndpointContext.instanceOutput, SignalSource.value]
        rw [All.inputIndex_input]]
      rw [componentOutputs component]
      apply (splitter.ports.outputs.signalType component).equal_eq_true_iff _ _ |>.mpr
      exact every component
  · rfl

noncomputable def aggregateCertification (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    ModuleCycleCertification
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := aggregateHasStructuralResult splitter components
  structuralResultUnique := aggregateHasAtMostOneSolution splitter components
  implements := aggregateImplements splitter components

noncomputable def aggregateImplementation (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implementation splitter.aggregateType :=
  (aggregateCertification splitter components).transportStructure
    (aggregateModuleStructure_eq splitter components).symm

private noncomputable def implementationDefinition :
    (signalType : SignalType) → Implementation signalType
  | .bit => bitCertification.transportStructure (by
      rw [moduleStructure])
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
    Implementation signalType := implementationDefinition signalType

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) := (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType := rfl

theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

end Silean2.Modules.Equality

namespace Silean2.Modules.Equality.Naming

open Silean2 Silean2.Naming

private def indexedComponent (signals : SignalMap) (component : signals.Label) :
    SourceName :=
  .scoped "equal" ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Equality.ports signalType) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .left | .right => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Equality.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Equality.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Equality.moduleStructure]
      unfold Modules.Equality.bitModuleStructure Certified.moduleStructure
      exact .composite ⟨"equality", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean2.Naming.Primitive.eq)
  | .vector length element, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : SignalSplitter := .vector length element
      exact .composite ⟨"equality", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => indexedComponent splitter.ports.outputs component
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inr (.inl component) =>
              namingWith element (typeNaming.component component)
          | .inr (.inr _) => All.Naming.naming (Modules.Equality.componentCount splitter))
  | .tuple fields, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨"equality", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => indexedComponent splitter.ports.outputs component
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inr (.inl component) =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .inr (.inr _) => All.Naming.naming (Modules.Equality.componentCount splitter))
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Equality.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

def namedModule (signalType : SignalType) : NamedModule where
  ports := Modules.Equality.ports signalType
  moduleStructure := Modules.Equality.moduleStructure signalType
  naming := naming signalType

end Silean2.Modules.Equality.Naming
