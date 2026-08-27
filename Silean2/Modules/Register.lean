import Silean2.CertifiedSchedule
import Silean2.Naming.PrimitiveNaming
import Silean2.Naming.SignalAdapterNaming
import Silean2.Primitives.Register
import Silean2.SignalAdapterCertified

namespace Silean2.Modules.Register

open Silean2

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Primitives.UnaryInput fun | .input => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Primitives.SingleOutput fun | .output => signalType

@[reducible] def stateMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Primitives.RegisterState fun | .stored => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

abbrev Rule := Primitives.RegisterRule

def outputRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) (stateMap signalType)
      { inputTypes := .nil
        outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .output
  target | (), state => (state .stored, ())

def stateRule (signalType : SignalType) :
    CycleStateRule (ports signalType) (stateMap signalType) where
  inputTypes := .cons signalType .nil
  readsInputs := (inputMap signalType).select .input
  target := fun | (input, ()), _ => fun | .stored => input

@[reducible] def cycleContract (signalType : SignalType) :
    ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

/-! The aggregate branch has one splitter, one recursively registered child
per immediate component, and one combiner. -/

abbrev AggregateInstance (splitter : SignalSplitter) :=
  Enumeration.Framed splitter.ports.outputs.Label

@[reducible] def aggregateInstanceEnumeration (splitter : SignalSplitter) :
    Enumeration (AggregateInstance splitter) :=
  Enumeration.framed splitter.ports.outputs.labels

@[reducible] def aggregateInstances (splitter : SignalSplitter) : Instances where
  Key := AggregateInstance splitter
  keys := aggregateInstanceEnumeration splitter
  value
    | .start => splitter.ports
    | .item component => ports (splitter.ports.outputs.signalType component)
    | .finish => splitter.combiner.ports

@[reducible] def aggregateContext (splitter : SignalSplitter) : EndpointContext where
  ports := ports splitter.aggregateType
  instances := aggregateInstances splitter

def aggregateWiring (splitter : SignalSplitter) :
    Wiring (aggregateContext splitter).ports (aggregateContext splitter).instances :=
  match splitter with
  | .vector length element => {
      moduleOutput := fun port => match port with
        | .output => (aggregateContext (.vector length element)).instanceOutput
            .finish AggregatePort.value
      instanceInput := fun
        | .start, AggregatePort.value =>
            (aggregateContext (.vector length element)).moduleInput .input
        | .item component, .input =>
            (aggregateContext (.vector length element)).instanceOutput
              .start component
        | .finish, component =>
            (aggregateContext (.vector length element)).instanceOutput
              (.item component) .output }
  | .tuple fields => {
      moduleOutput := fun port => match port with
        | .output => (aggregateContext (.tuple fields)).instanceOutput
            .finish AggregatePort.value
      instanceInput := fun
        | .start, AggregatePort.value =>
            (aggregateContext (.tuple fields)).moduleInput .input
        | .item component, .input =>
            (aggregateContext (.tuple fields)).instanceOutput .start component
        | .finish, component =>
            (aggregateContext (.tuple fields)).instanceOutput
              (.item component) .output }

@[reducible] def aggregateBody (splitter : SignalSplitter) : ModuleBody where
  context := aggregateContext splitter
  wiring := aggregateWiring splitter

theorem bit_ports : ports .bit = Primitives.register.ports := rfl
theorem bit_contract : cycleContract .bit = Primitives.registerCycleContract := rfl

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  | .bit => .primitive Primitives.register
  | .vector length element =>
      .composite (aggregateBody (.vector length element)) fun
        | .start => .splitter (.vector length element)
        | .item _ => moduleStructure element
        | .finish => .combiner (.vector length element)
  | .tuple fields =>
      .composite (aggregateBody (.tuple fields)) fun
        | .start => .splitter (.tuple fields)
        | .item component => moduleStructure (fields.typeAt component)
        | .finish => .combiner (.tuple fields)
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
  | .start => splitter.certified
  | .item component => (components component).certified
  | .finish => splitter.combiner.certified

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
      cases child <;> rfl
  | tuple fields =>
      simp only [SignalSplitter.aggregateType, moduleStructure,
        Certified.moduleStructure]
      congr
      funext child
      cases child <;> rfl

def aggregateStateCorresponds (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (contractState : (stateMap splitter.aggregateType).Values)
    (structuralState :
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) : Prop :=
  ∀ component,
    (components component).stateCorresponds
      (fun statePort => match statePort with
        | .stored => splitter.outputValues
            (splitter.inputValues (contractState .stored))
            component)
      (structuralState (.item component))

def bitImplementation : Implementation .bit := by
  have structureEq : Primitives.registerCertified.moduleStructure =
      moduleStructure .bit := by
    simp [Primitives.registerCertified, moduleStructure]
  have contractEq : Primitives.registerCertified.cycleContract =
      cycleContract .bit := by
    rw [show Primitives.registerCertified.cycleContract =
      Primitives.registerCycleContract by
        simp [Primitives.registerCertified]]
    exact bit_contract.symm
  exact Primitives.registerCertified.certification
    |>.transportStructure structureEq
    |>.transportContract contractEq

theorem aggregateHasCorrespondingState (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (structuralState :
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) :
    ∃ contractState,
      aggregateStateCorresponds splitter components contractState structuralState := by
  let Property := fun component contractState =>
    (components component).stateCorresponds contractState
      (structuralState (.item component))
  have available : ∀ component, ∃ contractState, Property component contractState :=
    fun component => (components component).hasCorrespondingState
      (structuralState (.item component))
  rcases splitter.ports.outputs.labels.exists_pi Property available with
    ⟨componentStates, correspond⟩
  let componentValues : splitter.ports.outputs.Values :=
    fun component => componentStates component .stored
  let contractState : (stateMap splitter.aggregateType).Values := fun
    | .stored => splitter.combineComponents componentValues
  refine ⟨contractState, ?_⟩
  intro component
  rw [show splitter.outputValues
      (splitter.inputValues (contractState .stored)) component =
        componentValues component by
    exact congrFun (splitter.split_combined componentValues) component]
  exact correspond component

def aggregateSplitterInputs (splitter : SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values :=
  splitter.inputValues (inputs .input)

def aggregateComponentInputs (splitter : SignalSplitter)
    (splitProposal : ProposedValues splitter.certified.moduleStructure)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values := fun
  | .input => splitProposal.outputs component

def aggregateCombinerInputs (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (componentProposals : (component : splitter.ports.outputs.Label) →
      ProposedValues
        (moduleStructure (splitter.ports.outputs.signalType component))) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter with
  | vector => exact fun component => (componentProposals component).outputs .output
  | tuple => exact fun component => (componentProposals component).outputs .output

def aggregateOutputs (splitter : SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .output => combineProposal.outputs .value
  | .tuple _ => fun | .output => combineProposal.outputs .value

theorem aggregateHasStructuralResult (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (structuralState :
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).IsSolution
          inputs structuralState proposal := by
  rcases splitter.certified.hasStructuralResult
      (aggregateSplitterInputs splitter inputs) (structuralState .start) with
    ⟨splitProposal, splitSatisfies⟩
  let Property := fun component proposal =>
    (moduleStructure (splitter.ports.outputs.signalType component)).IsSolution
      (aggregateComponentInputs splitter splitProposal component)
      (structuralState (.item component)) proposal
  have componentAvailable : ∀ component, ∃ proposal, Property component proposal :=
    fun component => (components component).hasStructuralResult
      (aggregateComponentInputs splitter splitProposal component)
      (structuralState (.item component))
  rcases splitter.ports.outputs.labels.exists_pi Property componentAvailable with
    ⟨componentProposals, componentSatisfies⟩
  rcases splitter.combiner.certified.hasStructuralResult
      (aggregateCombinerInputs splitter components componentProposals)
      (structuralState .finish) with ⟨combineProposal, combineSatisfies⟩
  let childProposals : (name : AggregateInstance splitter) →
      ProposedValues (aggregateChildStructure splitter components name)
    | .start => splitProposal
    | .item component => componentProposals component
    | .finish => combineProposal
  let outputs := aggregateOutputs splitter combineProposal
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro port
    cases port
    cases splitter <;> rfl
  · intro child
    cases child with
    | start =>
        change splitter.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals .start)
          (structuralState .start) splitProposal
        rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals .start =
            aggregateSplitterInputs splitter inputs by
          cases splitter <;> funext port <;> cases port <;> rfl]
        exact splitSatisfies
    | item component =>
        change (moduleStructure
          (splitter.ports.outputs.signalType component)).IsSolution
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals
              (.item component))
          (structuralState (.item component)) (componentProposals component)
        rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals
            (.item component) =
              aggregateComponentInputs splitter splitProposal component by
          cases splitter <;> funext port <;> cases port <;> rfl]
        exact componentSatisfies component
    | finish =>
        change splitter.combiner.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals .finish)
          (structuralState .finish) combineProposal
        rw [show ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter components) inputs childProposals .finish =
            aggregateCombinerInputs splitter components componentProposals by
          cases splitter <;> funext port <;> rfl]
        exact combineSatisfies

abbrev splitOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.start, SignalComponentRule.apply⟩

abbrev componentOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.item component, Primitives.RegisterRule.observe⟩

abbrev combineOccurrence (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleOccurrence (aggregateChildren splitter components) :=
  ⟨.finish, SignalComponentRule.apply⟩

theorem componentOccurrence_injective (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Function.Injective (componentOccurrence splitter components) := by
  intro left right equal
  have childEqual : Enumeration.Framed.item left =
      Enumeration.Framed.item right :=
    congrArg Certified.RuleOccurrence.child equal
  exact Enumeration.Framed.item.inj childEqual

noncomputable def componentOutputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun port => port ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ component, componentOccurrence splitter components component ∈ final) ∧
        ∀ called, called ∈ final → ∃ component,
          called = componentOccurrence splitter components component) [] :=
  Certified.Schedule.callFamily splitter.ports.outputs.labels
    (componentOccurrence splitter components)
    (componentOccurrence_injective splitter components)
    (by intro component port member
        change port ∈ (outputRule
          (splitter.ports.outputs.signalType component)).readsInputs.labels at member
        cases member)

noncomputable def aggregateOutputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .observe := by
  let family := componentOutputSchedule splitter components
  apply family.append
  refine .call (combineOccurrence splitter components) ?_ ?_ (.done ?_)
  · intro port inputMem
    cases splitter with
    | vector length element =>
        exact ⟨Primitives.RegisterRule.observe,
          family.finished.1 port,
          by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
    | tuple fields =>
        exact ⟨Primitives.RegisterRule.observe,
          family.finished.1 port,
          by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
  · intro member
    rcases family.finished.2 _ member with ⟨component, equal⟩
    cases equal
  · intro port outputMem
    cases splitter with
    | vector length element =>
        exact ⟨SignalComponentRule.apply, by simp,
          by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩
    | tuple fields =>
        exact ⟨SignalComponentRule.apply, by simp,
          by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩

def aggregateStateSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) :=
  .call (splitOccurrence splitter components)
    (by
      intro input inputMem
      cases splitter <;> cases input
      · trivial
      · trivial)
    (by simp)
    (.done (by
      intro child input member
      cases child with
      | start =>
          simp [aggregateChildren, SignalSplitter.certified,
            SignalSplitter.cycleContract, CycleStateRule.empty,
            SignalSelection.labels] at member
      | item component =>
          cases input
          cases splitter with
          | vector length element =>
              change Certified.outputAvailable
                ([splitOccurrence (.vector length element) components] :
                  Certified.Availability
                    (aggregateChildren (.vector length element) components))
                .start component
              exact ⟨SignalComponentRule.apply, by simp, by
                change component ∈
                  (SignalSplitter.vector length element).ports.outputs.allSelection.labels
                rw [SignalMap.allSelection_labels]
                exact ListIndex.get_eq
                  ((SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                    List.get_mem _ _⟩
          | tuple fields =>
              change Certified.outputAvailable
                ([splitOccurrence (.tuple fields) components] :
                  Certified.Availability
                    (aggregateChildren (.tuple fields) components))
                .start component
              exact ⟨SignalComponentRule.apply, by simp, by
                change component ∈
                  (SignalSplitter.tuple fields).ports.outputs.allSelection.labels
                rw [SignalMap.allSelection_labels]
                exact ListIndex.get_eq
                  ((SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                    List.get_mem _ _⟩
      | finish =>
          simp [aggregateChildren, SignalCombiner.certified,
            SignalCombiner.cycleContract, CycleStateRule.empty,
            SignalSelection.labels] at member))

noncomputable def aggregateRuleSchedules (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Certified.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType) where
  output | .observe => aggregateOutputSchedule splitter components
  state := aggregateStateSchedule splitter components

theorem component_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter components component ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  cases splitter with
  | vector length element =>
      unfold aggregateOutputSchedule
      rw [Certified.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.vector length element) components).finished.1 component)
  | tuple fields =>
      unfold aggregateOutputSchedule
      rw [Certified.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.tuple fields) components).finished.1 component)

theorem combine_mem_outputSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    combineOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  cases splitter <;> unfold aggregateOutputSchedule <;>
    rw [Certified.Schedule.finalAvailability_append] <;> exact List.mem_cons_self

theorem split_mem_stateSchedule (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    splitOccurrence splitter components ∈
      (aggregateStateSchedule splitter components).finalAvailability := by
  simp [aggregateStateSchedule, Certified.Schedule.finalAvailability]

theorem aggregateCoversChildren (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (aggregateRuleSchedules splitter components).CoversChildren := by
  intro child rule
  cases child with
  | start =>
      change SignalComponentRule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_includes
      exact split_mem_stateSchedule splitter components
  | item component =>
      change Primitives.RegisterRule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (aggregateRuleSchedules splitter components) .observe
      exact component_mem_outputSchedule splitter components component
  | finish =>
      change SignalComponentRule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (aggregateRuleSchedules splitter components) .observe
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
    (state : (stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .output = state .stored := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[reducible] def aggregateComponentContractState (splitter : SignalSplitter)
    (contractState : (stateMap splitter.aggregateType).Values)
    (component : splitter.ports.outputs.Label) :
    (stateMap (splitter.ports.outputs.signalType component)).Values := fun
  | .stored => splitter.outputValues
      (splitter.inputValues (contractState .stored)) component

private theorem aggregateImplements (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Implements
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter components) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  let Property := fun component nextState =>
    (cycleContract (splitter.ports.outputs.signalType component)).EvaluatesTo
      (ProposedValues.childInputs (aggregateBody splitter)
        (aggregateChildStructure splitter components) inputs childProposals
          (.item component))
      (aggregateComponentContractState splitter contractState component)
      (childProposals (.item component)).outputs nextState ∧
    (components component).stateCorresponds nextState
      (childProposals (.item component)).nextState
  have available : ∀ component, ∃ nextState, Property component nextState := by
    intro component
    exact (components component).implements _ _ _ _
      (corresponds component) (childSatisfies (.item component))
  rcases splitter.ports.outputs.labels.exists_pi Property available with
    ⟨componentNextStates, componentEvaluates⟩
  let nextContractState : (stateMap splitter.aggregateType).Values := fun
    | .stored => inputs .input
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      change outputs .output = contractState .stored
      have componentOutputs : ∀ component,
          (childProposals (.item component)).outputs .output =
            aggregateComponentContractState splitter contractState component .stored := by
        intro component
        have evaluated := (componentEvaluates component).1.1
          Primitives.RegisterRule.observe
        exact (outputRule_holds_iff _ _ _ _).mp evaluated
      have combineSatisfies := childSatisfies Enumeration.Framed.finish
      have boundaryOutput := boundary Primitives.SingleOutput.output
      cases splitter with
      | vector length element =>
          funext index
          have componentOutput := componentOutputs index
          simpa [ProposedValues.childInputs, aggregateBody, aggregateWiring,
            aggregateContext, aggregateInstances, aggregateComponentContractState,
            SignalSplitter.outputValues, SignalSplitter.inputValues,
            SignalCombiner.outputValues, SignalSource.value] using
            congrFun (boundaryOutput.trans
              (congrFun combineSatisfies AggregatePort.value)) index |>.trans
                componentOutput
      | tuple fields =>
          change (childProposals .finish).outputs =
            SignalCombiner.outputValues (.tuple fields)
              (ProposedValues.childInputs (aggregateBody (.tuple fields))
                (aggregateChildStructure (.tuple fields) components) inputs
                childProposals .finish) at combineSatisfies
          have combineInputs :
              ProposedValues.childInputs (aggregateBody (.tuple fields))
                (aggregateChildStructure (.tuple fields) components) inputs
                childProposals .finish =
              (fun component =>
                (childProposals (.item component)).outputs .output) := by
            funext component
            rfl
          rw [combineInputs] at combineSatisfies
          have boundaryOutput' : outputs .output =
              (childProposals .finish).outputs AggregatePort.value := by
            change outputs .output =
              (childProposals .finish).outputs AggregatePort.value at boundaryOutput
            exact boundaryOutput
          have combinedOutput :=
            congrFun combineSatisfies AggregatePort.value
          change (childProposals .finish).outputs AggregatePort.value =
            fields.assemble (fun component =>
              (childProposals (.item component)).outputs .output) at combinedOutput
          rw [boundaryOutput', combinedOutput]
          change fields.assemble (fun component =>
            (childProposals (.item component)).outputs .output) = contractState .stored
          have componentFunction : (fun component : SignalTypes.Position fields =>
              (childProposals (.item component)).outputs .output) =
              fields.get (contractState .stored) := by
            funext component
            exact componentOutputs component
          rw [componentFunction]
          exact fields.assemble_get (contractState .stored)
    · rfl
  · intro component
    have nextCorresponds := (componentEvaluates component).2
    have stateEvaluates := (componentEvaluates component).1.2
    change (components component).stateCorresponds
      (aggregateComponentContractState splitter nextContractState component)
      (childProposals (.item component)).nextState
    rw [show aggregateComponentContractState splitter nextContractState component =
        componentNextStates component by
      funext statePort
      cases statePort
      have nextValue : componentNextStates component .stored =
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals
              (.item component)) .input := by
        simpa [stateRule, CycleStateRule.apply, SignalSelection.project,
          SignalMap.select] using
          congrFun stateEvaluates Primitives.RegisterState.stored
      have splitSatisfies := childSatisfies Enumeration.Framed.start
      have childInputValue :
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals
              (.item component)) .input =
          splitter.outputValues (splitter.inputValues (inputs .input)) component := by
        cases splitter <;> exact congrFun splitSatisfies component
      exact childInputValue.symm.trans nextValue.symm]
    exact nextCorresponds

noncomputable def aggregateCertification (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    ModuleCycleCertification
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) where
  stateCorresponds := aggregateStateCorresponds splitter components
  hasCorrespondingState := aggregateHasCorrespondingState splitter components
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
    ModuleCycleCertified (ports signalType) :=
  (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  rfl

end Silean2.Modules.Register

namespace Silean2.Modules.Register.Naming

open Silean2 Silean2.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Register.ports signalType) where
  inputs := ⟨fun | .input => "in"⟩
  outputs := ⟨fun | .output => "out"⟩
  inputTypes := fun | .input => typeNaming
  outputTypes := fun | .output => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Register.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

private def componentName (splitter : SignalSplitter)
    (component : splitter.ports.outputs.Label) : SourceName :=
  .scoped "register"
    ((SignalMapNaming.indexed splitter.ports.outputs "component").name component)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Register.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Register.moduleStructure]
      exact Silean2.Naming.Primitive.register
  | .vector length element, typeNaming => by
      rw [Modules.Register.moduleStructure]
      let splitter : SignalSplitter := .vector length element
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .start => "split"
          | .item component => componentName splitter component
          | .finish => "combine")
        (fun
          | .start => Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .item component => namingWith element (typeNaming.component component)
          | .finish => Silean2.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.Register.moduleStructure]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .start => "split"
          | .item component => componentName splitter component
          | .finish => "combine")
        (fun
          | .start => Silean2.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .item component =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .finish => Silean2.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean2.Modules.Register.Naming
