import Silean.Contracts.Cycle.CycleLayerConstruction
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

@[reducible] def componentContracts (splitter : Composition.SignalSplitter) :
    (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (ports (splitter.ports.outputs.signalType component)) :=
  fun component => cycleContract (splitter.ports.outputs.signalType component)

@[reducible] def aggregateChildContracts (splitter : Composition.SignalSplitter) :=
  interface.aggregateChildContracts splitter (componentContracts splitter)

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

def aggregateSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values :=
  splitter.inputValues (inputs .input)

abbrev splitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.splitterOccurrence splitter
    (componentContracts splitter) .unit

abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.componentOccurrence splitter
    (componentContracts splitter) component
      Primitives.RegisterRule.observe

abbrev combineOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.combinerOccurrence splitter
    (componentContracts splitter) .output

noncomputable def componentOutputSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun port => port ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter component ∈ final) ∧
        ∀ called, called ∈ final → called ∈ [] ∨ ∃ component,
          called = componentOccurrence splitter component) [] :=
  interface.callComponentsAfter splitter
    (componentContracts splitter)
    ([] : Contracts.Cycle.Certification.Layer.Availability
      (aggregateBody splitter) (aggregateChildContracts splitter))
    (fun _ => Primitives.RegisterRule.observe)
    (by intro component member; contradiction)
    (by intro component port member
        change port ∈ (outputRule
          (splitter.ports.outputs.signalType component)).readsInputs.labels at member
        cases member)

noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.OutputSchedule (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType)
      .observe := by
  let family := componentOutputSchedule splitter
  apply family.append
  refine .call (combineOccurrence splitter) ?_ ?_ (.done ?_)
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

def aggregateStateSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.StateSchedule (aggregateBody splitter)
      (aggregateChildContracts splitter) :=
  .call (splitOccurrence splitter)
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
            simp [aggregateChildContracts,
              Composition.LeafwiseInterface.aggregateChildContracts,
              Composition.SignalSplitter.cycleContract, Contracts.Cycle.CycleStateRule.empty,
              SignalSelection.labels] at member
      | component component =>
          cases input
          cases splitter with
          | vector length element =>
              change Contracts.Cycle.Certification.Layer.outputAvailable
                ([splitOccurrence (.vector length element)] :
                  Contracts.Cycle.Certification.Layer.Availability
                    (aggregateBody (.vector length element))
                    (aggregateChildContracts (.vector length element)))
                (.splitter .unit) component
              exact ⟨Composition.SignalComponentRule.apply, by simp, by
                change component ∈
                  (Composition.SignalSplitter.vector length element).ports.outputs.allSelection.labels
                rw [SignalMap.allSelection_labels]
                exact ListIndex.get_eq
                  ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                    List.get_mem _ _⟩
          | tuple fields =>
              change Contracts.Cycle.Certification.Layer.outputAvailable
                ([splitOccurrence (.tuple fields)] :
                  Contracts.Cycle.Certification.Layer.Availability
                    (aggregateBody (.tuple fields))
                    (aggregateChildContracts (.tuple fields)))
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
          simp [aggregateChildContracts,
            Composition.LeafwiseInterface.aggregateChildContracts,
            Composition.SignalCombiner.cycleContract, Contracts.Cycle.CycleStateRule.empty,
            SignalSelection.labels] at member))

noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) where
  output | .observe => aggregateOutputSchedule splitter
  state := aggregateStateSchedule splitter

theorem component_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter component ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  cases splitter with
  | vector length element =>
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.vector length element)).finished.2.1 component)
  | tuple fields =>
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentOutputSchedule (.tuple fields)).finished.2.1 component)

theorem combine_mem_outputSchedule (splitter : Composition.SignalSplitter) :
    combineOccurrence splitter ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  cases splitter <;> unfold aggregateOutputSchedule <;>
    rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append] <;> exact List.mem_cons_self

theorem split_mem_stateSchedule (splitter : Composition.SignalSplitter) :
    splitOccurrence splitter ∈
      (aggregateStateSchedule splitter).finalAvailability := by
  simp [aggregateStateSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren := by
  intro child rule
  cases child with
  | splitter input =>
      cases input
      change Composition.SignalComponentRule at rule
      cases rule
      left
      exact split_mem_stateSchedule splitter
  | component component =>
      change Primitives.RegisterRule at rule
      cases rule
      right
      refine ⟨.observe, ?_⟩
      exact component_mem_outputSchedule splitter component
  | combiner outputName =>
      cases outputName
      change Composition.SignalComponentRule at rule
      cases rule
      right
      refine ⟨.observe, ?_⟩
      exact combine_mem_outputSchedule splitter

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

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (layerChildren : (child : (aggregateBody splitter).context.instancePorts.Name) →
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
    Contracts.Cycle.Implements
      (aggregateCertificationStructure splitter layerChildren)
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  have boundary := satisfies.1
  let Property := fun component nextState =>
    (cycleContract (splitter.ports.outputs.signalType component)).EvaluatesTo
      (ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.component component))
      (aggregateComponentContractState splitter contractState component)
      (childProposals (.component component)).outputs nextState ∧
    (layerChildren
      (.component component)).certification.stateCorresponds nextState
      (childProposals (.component component)).nextState
  have available : ∀ component, ∃ nextState, Property component nextState := by
    intro component
    exact (layerChildren
      (.component component)).certification.implements _ _ _ _
      (corresponds component) (satisfies.2 (.component component))
  rcases splitter.ports.outputs.labels.exists_pi Property available with
    ⟨componentNextStates, componentEvaluates⟩
  have combineOutputs : (childProposals (.combiner .output)).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.combiner .output)) := by
    letI : Subsingleton
        (aggregateChildContracts splitter (.combiner .output)).state.Values := by
      change Subsingleton emptySignalMap.Values
      infer_instance
    have evaluates :=
      (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
        (layerChildren) inputs structuralState
          (ProposedValues.composite outputs childProposals) satisfies
          (.combiner .output) SignalMap.emptyValues).1
    exact (Composition.SignalCombiner.outputRule_holds_iff splitter.combiner _ _ _).mp
      (evaluates.1 Composition.SignalComponentRule.apply)
  have splitOutputs : (childProposals (.splitter .unit)).outputs =
      splitter.outputValues (aggregateSplitterInputs splitter inputs) := by
    letI : Subsingleton
        (aggregateChildContracts splitter (.splitter .unit)).state.Values := by
      change Subsingleton emptySignalMap.Values
      infer_instance
    have evaluates :=
      (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
        (layerChildren) inputs structuralState
          (ProposedValues.composite outputs childProposals) satisfies
          (.splitter .unit) SignalMap.emptyValues).1
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      (evaluates.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.splitter .unit) = aggregateSplitterInputs splitter inputs := by
      cases splitter <;> funext port <;> cases port <;> rfl
    change (childProposals (.splitter .unit)).outputs =
      splitter.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.splitter .unit)) at holds
    rw [inputsEqual] at holds
    exact holds
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
              (congrFun combineOutputs Composition.AggregatePort.value)) index |>.trans
                componentOutput
      | tuple fields =>
          change (childProposals (.combiner .output)).outputs =
            Composition.SignalCombiner.outputValues (.tuple fields)
              (ProposedValues.childInputs (aggregateBody (.tuple fields))
                ((fun name => (layerChildren name).moduleStructure)) inputs
                childProposals (.combiner .output)) at combineOutputs
          have combineInputs :
              ProposedValues.childInputs (aggregateBody (.tuple fields))
                ((fun name => (layerChildren name).moduleStructure)) inputs
                childProposals (.combiner .output) =
              (fun component =>
                (childProposals (.component component)).outputs .output) := by
            funext component
            rfl
          rw [combineInputs] at combineOutputs
          have boundaryOutput' : outputs .output =
              (childProposals (.combiner .output)).outputs Composition.AggregatePort.value := by
            change outputs .output =
              (childProposals (.combiner .output)).outputs Composition.AggregatePort.value at boundaryOutput
            exact boundaryOutput
          have combinedOutput :=
            congrFun combineOutputs Composition.AggregatePort.value
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
    change (layerChildren
      (.component component)).certification.stateCorresponds
      (aggregateComponentContractState splitter nextContractState component)
      (childProposals (.component component)).nextState
    rw [show aggregateComponentContractState splitter nextContractState component =
        componentNextStates component by
      funext statePort
      cases statePort
      have nextValue : componentNextStates component .stored =
          (ProposedValues.childInputs (aggregateBody splitter)
            ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
              (.component component)) .input := by
        simpa [stateRule, Contracts.Cycle.CycleStateRule.apply, SignalSelection.project,
          SignalMap.select] using
          congrFun stateEvaluates Primitives.RegisterState.stored
      have childInputValue :
          (ProposedValues.childInputs (aggregateBody splitter)
            ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
              (.component component)) .input =
          splitter.outputValues (splitter.inputValues (inputs .input)) component := by
        cases splitter <;> exact congrFun splitOutputs component
      exact childInputValue.symm.trans nextValue.symm]
    exact nextCorresponds

end AggregateLayerCertification

noncomputable opaque aggregateCertifiedLayer (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (aggregateRuleSchedules splitter) (aggregateCoversChildren splitter)
    (aggregateStateCorresponds splitter) (aggregateHasCorrespondingState splitter)
    (aggregateImplements splitter)

@[reducible] noncomputable def aggregateCertifiedChildren
    (splitter : Composition.SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)) :
    (child : (aggregateBody splitter).context.instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter child)
  | .splitter _ => ⟨.splitter splitter, splitter.certified.certification⟩
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
