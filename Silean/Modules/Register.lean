import Silean.Contracts.Cycle.CycleSchedule
import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.RegisterPrimitive
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Modules.Register

open Silean

/-! A register for any signal type. Aggregate registers are recursively built
from registers for their component signal types. -/

@[reducible] def interface : Composition.LeafwiseInterface where
  Input := Primitives.UnaryInput
  inputs := inferInstance
  RecursiveInput := PUnit
  recursiveInputs := Enumeration.punit
  FixedInput := NoSignal
  fixedInputs := inferInstance
  inputLayout := {
    classify := fun | .input => .inl .unit
    label := fun | .inl _ => .input | .inr impossible => nomatch impossible
    classify_label := by intro part; cases part with
      | inl value => cases value; rfl
      | inr impossible => exact nomatch impossible
    label_classify := by intro inputName; cases inputName; rfl }
  fixedInputType := fun impossible => nomatch impossible
  Output := Primitives.SingleOutput
  outputs := inferInstance
  State := Primitives.RegisterState
  states := inferInstance

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  interface.inputMap signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  interface.outputMap signalType

@[reducible] def stateMap (signalType : SignalType) : SignalMap :=
  interface.stateMap signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  interface.ports signalType

abbrev Rule := Primitives.RegisterRule

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType)
      { inputTypes := .nil
        outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .output
  target | (), state => (state .stored, ())

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (ports signalType) (stateMap signalType) where
  inputTypes := .cons signalType .nil
  readsInputs := (inputMap signalType).select .input
  target := fun | (input, ()), _ => fun | .stored => input

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

@[reducible] def aggregateBody (splitter : Composition.SignalSplitter) :=
  interface.aggregateBody splitter

theorem bit_ports : ports .bit = Primitives.register.ports := rfl
theorem bit_contract : cycleContract .bit = Primitives.registerCycleContract := rfl

/-! ## Hardware structure

A bit is one register primitive. A vector or tuple is split into its immediate
components, registered recursively, and recombined with the same shape. -/

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  := interface.moduleStructure (.primitive Primitives.register)

abbrev Implementation (signalType : SignalType) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

def Implementation.certified (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

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
      cases child <;> rfl
  | tuple fields =>
      rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_3]
      simp only [Composition.SignalSplitter.aggregateType, Contracts.Cycle.Certification.moduleStructure]
      congr
      funext child
      cases child <;> rfl

def aggregateStateCorresponds (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (contractState : (stateMap splitter.aggregateType).Values)
    (structuralState :
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) : Prop :=
  ∀ component,
    (components component).stateCorresponds
      (fun statePort => match statePort with
        | .stored => splitter.outputValues
            (splitter.inputValues (contractState .stored))
            component)
      (structuralState (.component component))

def bitImplementation : Implementation .bit := by
  have structureEq : Primitives.registerCertified.moduleStructure =
      moduleStructure .bit := by
    rw [moduleStructure, Composition.LeafwiseInterface.moduleStructure.eq_1]
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

theorem aggregateHasCorrespondingState (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (structuralState :
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) :
    ∃ contractState,
      aggregateStateCorresponds splitter components contractState structuralState := by
  let Property := fun component contractState =>
    (components component).stateCorresponds contractState
      (structuralState (.component component))
  have available : ∀ component, ∃ contractState, Property component contractState :=
    fun component => (components component).hasCorrespondingState
      (structuralState (.component component))
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

def aggregateSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values :=
  splitter.inputValues (inputs .input)

def aggregateComponentInputs (splitter : Composition.SignalSplitter)
    (splitProposal : ProposedValues splitter.certified.moduleStructure)
    (component : splitter.ports.outputs.Label) :
    (ports (splitter.ports.outputs.signalType component)).inputs.Values := fun
  | .input => splitProposal.outputs component

def aggregateCombinerInputs (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (componentProposals : (component : splitter.ports.outputs.Label) →
      ProposedValues
        (moduleStructure (splitter.ports.outputs.signalType component))) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter with
  | vector => exact fun component => (componentProposals component).outputs .output
  | tuple => exact fun component => (componentProposals component).outputs .output

def aggregateOutputs (splitter : Composition.SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .output => combineProposal.outputs .value
  | .tuple _ => fun | .output => combineProposal.outputs .value

def aggregateProposalConstruction (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    interface.AggregateProposalConstruction splitter
      (fun component => (components component).certified) where
  splitterInputs inputs _ := aggregateSplitterInputs splitter inputs
  componentInputs _ splitProposals component :=
    aggregateComponentInputs splitter (splitProposals .unit) component
  combinerInputs componentProposals _ :=
    aggregateCombinerInputs splitter components componentProposals
  outputs combineProposals := aggregateOutputs splitter (combineProposals .output)
  boundary_eq := by
    intro inputs splitProposals componentProposals combineProposals outputName
    cases outputName
    cases splitter <;> rfl
  splitterInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals recursiveInput
    cases recursiveInput
    cases splitter <;> funext port <;> cases port <;> rfl
  componentInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals component
    cases splitter <;> funext port <;> cases port <;> rfl
  combinerInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals outputName
    cases outputName
    cases splitter <;> funext port <;> rfl

theorem aggregateHasStructuralResult (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (structuralState :
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components)).IsSolution
          inputs structuralState proposal := by
  exact (aggregateProposalConstruction splitter components).hasStructuralResult
    inputs structuralState

abbrev splitOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.splitterOccurrence splitter
    (fun component => (components component).certified) .unit

abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.componentOccurrence splitter
    (fun component => (components component).certified) component
      Primitives.RegisterRule.observe

abbrev combineOccurrence (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleOccurrence (aggregateChildren splitter components) :=
  interface.combinerOccurrence splitter
    (fun component => (components component).certified) .output

noncomputable def componentOutputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.Schedule (aggregateBody splitter)
      (aggregateChildren splitter components)
      (fun port => port ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter components component ∈ final) ∧
        ∀ called, called ∈ final → called ∈ [] ∨ ∃ component,
          called = componentOccurrence splitter components component) [] :=
  interface.callComponentsAfter splitter
    (fun component => (components component).certified)
    ([] : Contracts.Cycle.Certification.Availability (aggregateChildren splitter components))
    (fun _ => Primitives.RegisterRule.observe)
    (by intro component member; contradiction)
    (by intro component port member
        change port ∈ (outputRule
          (splitter.ports.outputs.signalType component)).readsInputs.labels at member
        cases member)

noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType)
      .observe := by
  let family := componentOutputSchedule splitter components
  apply family.append
  refine .call (combineOccurrence splitter components) ?_ ?_ (.done ?_)
  · intro port inputMem
    cases splitter with
    | vector length element =>
        exact ⟨Primitives.RegisterRule.observe,
          family.finished.2.1 port,
          by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
    | tuple fields =>
        exact ⟨Primitives.RegisterRule.observe,
          family.finished.2.1 port,
          by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
  · intro member
    rcases family.finished.2.2 _ member with impossible | ⟨component, equal⟩
    · contradiction
    · cases equal
  · intro port outputMem
    cases splitter with
    | vector length element =>
        exact ⟨Composition.SignalComponentRule.apply, by simp,
          by change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]; simp⟩
    | tuple fields =>
        exact ⟨Composition.SignalComponentRule.apply, by simp,
          by change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]; simp⟩

def aggregateStateSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.StateSchedule (aggregateBody splitter)
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
      | splitter recursiveInput =>
          cases recursiveInput
          cases splitter <;>
            change Composition.AggregatePort at input <;>
            cases input <;>
            simp [aggregateChildren, Composition.LeafwiseInterface.aggregateChildren,
              Composition.SignalSplitter.certified,
              Composition.SignalSplitter.cycleContract, Contracts.Cycle.CycleStateRule.empty,
              SignalSelection.labels] at member
      | component component =>
          cases input
          cases splitter with
          | vector length element =>
              change Contracts.Cycle.Certification.outputAvailable
                ([splitOccurrence (.vector length element) components] :
                  Contracts.Cycle.Certification.Availability
                    (aggregateChildren (.vector length element) components))
                (.splitter .unit) component
              exact ⟨Composition.SignalComponentRule.apply, by simp, by
                change component ∈
                  (Composition.SignalSplitter.vector length element).ports.outputs.allSelection.labels
                rw [SignalMap.allSelection_labels]
                exact ListIndex.get_eq
                  ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                    List.get_mem _ _⟩
          | tuple fields =>
              change Contracts.Cycle.Certification.outputAvailable
                ([splitOccurrence (.tuple fields) components] :
                  Contracts.Cycle.Certification.Availability
                    (aggregateChildren (.tuple fields) components))
                (.splitter .unit) component
              exact ⟨Composition.SignalComponentRule.apply, by simp, by
                change component ∈
                  (Composition.SignalSplitter.tuple fields).ports.outputs.allSelection.labels
                rw [SignalMap.allSelection_labels]
                exact ListIndex.get_eq
                  ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                    List.get_mem _ _⟩
      | combiner outputName =>
          cases outputName
          simp [aggregateChildren, Composition.LeafwiseInterface.aggregateChildren,
            Composition.SignalCombiner.certified,
            Composition.SignalCombiner.cycleContract, Contracts.Cycle.CycleStateRule.empty,
            SignalSelection.labels] at member))

noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Certification.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter components) (cycleContract splitter.aggregateType) where
  output | .observe => aggregateOutputSchedule splitter components
  state := aggregateStateSchedule splitter components

theorem component_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter components component ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  cases splitter with
  | vector length element =>
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.vector length element) components).finished.2.1 component)
  | tuple fields =>
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.tuple fields) components).finished.2.1 component)

theorem combine_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    combineOccurrence splitter components ∈
      (aggregateOutputSchedule splitter components).finalAvailability := by
  cases splitter <;> unfold aggregateOutputSchedule <;>
    rw [Contracts.Cycle.Certification.Schedule.finalAvailability_append] <;> exact List.mem_cons_self

theorem split_mem_stateSchedule (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    splitOccurrence splitter components ∈
      (aggregateStateSchedule splitter components).finalAvailability := by
  simp [aggregateStateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

theorem aggregateCoversChildren (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (aggregateRuleSchedules splitter components).CoversChildren := by
  intro child rule
  cases child with
  | splitter input =>
      cases input
      change Composition.SignalComponentRule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
      exact split_mem_stateSchedule splitter components
  | component component =>
      change Primitives.RegisterRule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
      apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs
        (aggregateRuleSchedules splitter components) .observe
      exact component_mem_outputSchedule splitter components component
  | combiner outputName =>
      cases outputName
      change Composition.SignalComponentRule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
      apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs
        (aggregateRuleSchedules splitter components) .observe
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
    (state : (stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .output = state .stored := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[reducible] def aggregateComponentContractState (splitter : Composition.SignalSplitter)
    (contractState : (stateMap splitter.aggregateType).Values)
    (component : splitter.ports.outputs.Label) :
    (stateMap (splitter.ports.outputs.signalType component)).Values := fun
  | .stored => splitter.outputValues
      (splitter.inputValues (contractState .stored)) component

private theorem aggregateImplements (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
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
          (.component component))
      (aggregateComponentContractState splitter contractState component)
      (childProposals (.component component)).outputs nextState ∧
    (components component).stateCorresponds nextState
      (childProposals (.component component)).nextState
  have available : ∀ component, ∃ nextState, Property component nextState := by
    intro component
    exact (components component).implements _ _ _ _
      (corresponds component) (childSatisfies (.component component))
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
          (childProposals (.component component)).outputs .output =
            aggregateComponentContractState splitter contractState component .stored := by
        intro component
        have evaluated := (componentEvaluates component).1.1
          Primitives.RegisterRule.observe
        exact (outputRule_holds_iff _ _ _ _).mp evaluated
      have combineSatisfies := childSatisfies ((.combiner .output))
      have boundaryOutput := boundary Primitives.SingleOutput.output
      cases splitter with
      | vector length element =>
          funext index
          have componentOutput := componentOutputs index
          simpa [ProposedValues.childInputs, aggregateBody,
            Composition.LeafwiseInterface.aggregateWiring,
            Composition.LeafwiseInterface.aggregateContext,
            Composition.LeafwiseInterface.aggregateInstances, aggregateComponentContractState,
            Composition.SignalSplitter.outputValues, Composition.SignalSplitter.inputValues,
            Composition.SignalCombiner.outputValues, SignalSource.value] using
            congrFun (boundaryOutput.trans
              (congrFun combineSatisfies Composition.AggregatePort.value)) index |>.trans
                componentOutput
      | tuple fields =>
          change (childProposals (.combiner .output)).outputs =
            Composition.SignalCombiner.outputValues (.tuple fields)
              (ProposedValues.childInputs (aggregateBody (.tuple fields))
                (aggregateChildStructure (.tuple fields) components) inputs
                childProposals (.combiner .output)) at combineSatisfies
          have combineInputs :
              ProposedValues.childInputs (aggregateBody (.tuple fields))
                (aggregateChildStructure (.tuple fields) components) inputs
                childProposals (.combiner .output) =
              (fun component =>
                (childProposals (.component component)).outputs .output) := by
            funext component
            rfl
          rw [combineInputs] at combineSatisfies
          have boundaryOutput' : outputs .output =
              (childProposals (.combiner .output)).outputs Composition.AggregatePort.value := by
            change outputs .output =
              (childProposals (.combiner .output)).outputs Composition.AggregatePort.value at boundaryOutput
            exact boundaryOutput
          have combinedOutput :=
            congrFun combineSatisfies Composition.AggregatePort.value
          change (childProposals (.combiner .output)).outputs Composition.AggregatePort.value =
            fields.assemble (fun component =>
              (childProposals (.component component)).outputs .output) at combinedOutput
          rw [boundaryOutput', combinedOutput]
          change fields.assemble (fun component =>
            (childProposals (.component component)).outputs .output) = contractState .stored
          have componentFunction : (fun component : SignalTypes.Position fields =>
              (childProposals (.component component)).outputs .output) =
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
      (childProposals (.component component)).nextState
    rw [show aggregateComponentContractState splitter nextContractState component =
        componentNextStates component by
      funext statePort
      cases statePort
      have nextValue : componentNextStates component .stored =
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals
              (.component component)) .input := by
        simpa [stateRule, Contracts.Cycle.CycleStateRule.apply, SignalSelection.project,
          SignalMap.select] using
          congrFun stateEvaluates Primitives.RegisterState.stored
      have splitSatisfies := childSatisfies ((.splitter .unit))
      have childInputValue :
          (ProposedValues.childInputs (aggregateBody splitter)
            (aggregateChildStructure splitter components) inputs childProposals
              (.component component)) .input =
          splitter.outputValues (splitter.inputValues (inputs .input)) component := by
        cases splitter <;> exact congrFun splitSatisfies component
      exact childInputValue.symm.trans nextValue.symm]
    exact nextCorresponds

noncomputable def aggregateCertification (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter components))
      (cycleContract splitter.aggregateType) where
  stateCorresponds := aggregateStateCorresponds splitter components
  hasCorrespondingState := aggregateHasCorrespondingState splitter components
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
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  rfl

end Silean.Modules.Register

namespace Silean.Modules.Register.Naming

open Silean Silean.Naming

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

private def componentName (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) : SourceName :=
  .scoped "register"
    ((SignalMapNaming.indexed splitter.ports.outputs "component").name component)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Register.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Register.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_1]
      exact Silean.Naming.Primitive.register
  | .vector length element, typeNaming => by
      rw [Modules.Register.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_2]
      let splitter : Composition.SignalSplitter := .vector length element
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => componentName splitter component
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component => namingWith element (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.Register.moduleStructure,
        Composition.LeafwiseInterface.moduleStructure.eq_3]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => componentName splitter component
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.Register.Naming
