import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.LeafwiseComposition
import Silean.Composition.SignalLogic
import Silean.Primitives.PrimitivePorts

namespace Silean.Composition.BinaryLeafwise

open Silean

/-! A single certified construction for binary operations lifted leafwise over
bits, vectors, and tuples. A module supplies the natural Lean operation and a
certified one-bit gate; this file owns the recursive hardware, schedules, and
certification proof. -/

class Operation where
  /-- Natural Lean behavior of the operation at every signal shape. -/
  apply : (signalType : SignalType) →
    signalType.Denote → signalType.Denote → signalType.Denote
  /-- Splitting an aggregate result agrees with applying the operation to each
  pair of immediate components. -/
  split_apply : ∀ (splitter : SignalSplitter)
      (left right : splitter.aggregateType.Denote),
    splitter.outputValues
        (splitter.inputValues (apply splitter.aggregateType left right)) =
      fun component =>
        apply (splitter.ports.outputs.signalType component)
          (splitter.outputValues (splitter.inputValues left) component)
          (splitter.outputValues (splitter.inputValues right) component)

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

def outputRule [operation : Operation] (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((inputMap signalType).select .right).prepend .left
  writesOutputs := (outputMap signalType).select .result
  target | (left, (right, ())), _ => (operation.apply signalType left right, ())

@[reducible] def cycleContract [Operation] (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

/-- The certified one-bit gate used at the leaves. Its public rule must be the
ordinary two-input, one-output, stateless binary operation. -/
class BitGate (operation : Operation) where
  cycleContract : Contracts.Cycle.ModuleCycleContract Primitives.binaryPorts
  certified : Contracts.Cycle.ModuleCycleCertifiedStructure cycleContract
  rule : cycleContract.RuleName
  everyRule : ∀ candidate, candidate = rule
  reads : (cycleContract.outputRule rule).2.readsInputs.labels = [.left, .right]
  writes : (cycleContract.outputRule rule).2.writesOutputs.labels = [.output]
  state : cycleContract.state.Values
  stateSubsingleton : Subsingleton cycleContract.state.Values
  stateReadsEmpty : cycleContract.stateRule.readsInputs.labels = []
  output_eq : ∀ inputs state outputs,
    (cycleContract.outputRule rule).2.Holds inputs state outputs →
      outputs .output = operation.apply .bit (inputs .left) (inputs .right)

section Construction

variable [operation : Operation] [gate : BitGate operation]

/-! ## Hardware structure -/

inductive BitInstance
  /-- The supplied one-bit primitive or certified module. -/
  | gate
deriving Enumeration

@[reducible] def bitInstances : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.binaryPorts

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instancePorts where
  -- The gate result is the boundary result.
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  -- Both operands feed the supplied gate.
  instanceInput
    | .gate, .left => bitContext.moduleInput .left
    | .gate, .right => bitContext.moduleInput .right

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildContracts : Contracts.Cycle.ChildCycleContracts bitBody
  | .gate => gate.cycleContract

@[reducible] def bitStructuralChildren :
  (child : bitInstances.Name) → ModuleStructure (bitInstances.ports child)
  | .gate => gate.certified.moduleStructure

@[reducible] noncomputable def bitCertifiedChildren :
    (child : bitInstances.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child)
  | .gate => gate.certified

def bitModuleStructure : ModuleStructure (ports .bit) :=
  .composite bitBody bitStructuralChildren

abbrev bitRule : Contracts.Cycle.Certification.Layer.RuleOccurrence
    bitBody bitChildContracts :=
  ⟨.gate, gate.rule⟩

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
      exact ⟨gate.rule, by simp,
        by change Primitives.SingleOutput.output ∈
           (gate.cycleContract.outputRule gate.rule).2.writesOutputs.labels
           rw [gate.writes]
           exact List.mem_cons_self⟩))

def bitStateSchedule : Contracts.Cycle.Certification.Layer.StateSchedule
    bitBody bitChildContracts :=
  .done (by
    intro child input member
    cases child
    change input ∈ gate.cycleContract.stateRule.readsInputs.labels at member
    rw [gate.stateReadsEmpty] at member
    cases member)

def bitRuleSchedules : Contracts.Cycle.Certification.Layer.RuleSchedules
    bitBody bitChildContracts
    (cycleContract .bit) where
  output | .apply => bitOutputSchedule
  state := bitStateSchedule

theorem bitCoversChildren : bitRuleSchedules.CoversChildren := by
  intro child rule
  right
  cases child
  rw [gate.everyRule rule]
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
  letI : Subsingleton ((bitChildContracts .gate).state.Values) :=
    gate.stateSubsingleton
  have gateEvaluates :=
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal
        satisfies .gate gate.state).1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [show (outputRule .bit).Holds inputs contractState proposal.outputs ↔
        proposal.outputs .result = operation.apply .bit
          (inputs .left) (inputs .right) by
      simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
        SignalSelection.project, SignalSelection.prepend, SignalMap.select]]
    rcases proposal with ⟨outputs, children⟩
    have boundary := satisfies.1
    change outputs .result = operation.apply .bit (inputs .left) (inputs .right)
    have boundaryResult := boundary .result
    change outputs .result = (children .gate).outputs .output at boundaryResult
    have gateOutput : (children .gate).outputs .output =
        operation.apply .bit (inputs .left) (inputs .right) :=
      gate.output_eq _ _ _ (gateEvaluates.1 gate.rule)
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
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

def Implementation.certified (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

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

abbrev leftSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.splitterOccurrence splitter (componentContracts splitter) .left

abbrev rightSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  interface.splitterOccurrence splitter (componentContracts splitter) .right

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

omit gate in
@[simp] theorem leftSplitOccurrence_writes (splitter : Composition.SignalSplitter) :
    (leftSplitOccurrence splitter).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

omit gate in
@[simp] theorem rightSplitOccurrence_writes (splitter : Composition.SignalSplitter) :
    (rightSplitOccurrence splitter).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

noncomputable def componentSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈
          [rightSplitOccurrence splitter, leftSplitOccurrence splitter] →
            called ∈ final) ∧
        (∀ component, componentOccurrence splitter component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [rightSplitOccurrence splitter, leftSplitOccurrence splitter] ∨
          ∃ component, called = componentOccurrence splitter component)
      [rightSplitOccurrence splitter, leftSplitOccurrence splitter] :=
  interface.callComponentsAfter splitter (componentContracts splitter)
    [rightSplitOccurrence splitter, leftSplitOccurrence splitter]
    (fun _ => Rule.apply)
    (by
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg
          Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro component input _
      cases input with
      | left =>
          cases splitter with
          | vector length element =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [leftSplitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [leftSplitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩
      | right =>
          cases splitter with
          | vector length element =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [rightSplitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.vector length element).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩
          | tuple fields =>
              exact ⟨Composition.SignalComponentRule.apply, by simp,
                by rw [rightSplitOccurrence_writes]
                   exact ListIndex.get_eq
                     ((Composition.SignalSplitter.tuple fields).ports.outputs.labels.locate component) ▸
                       List.get_mem _ _⟩)

noncomputable def aggregateAfterSplitsSchedule
    (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Contracts.Cycle.Certification.Layer.BoundaryReady
        (aggregateBody splitter) (aggregateChildContracts splitter)
        (outputRule splitter.aggregateType).writesOutputs.labels
        (fun input => input ∈
          (outputRule splitter.aggregateType).readsInputs.labels))
      [rightSplitOccurrence splitter, leftSplitOccurrence splitter] := by
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
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at atStart
      rcases atStart with equal | equal <;>
        have childEqual := congrArg
          Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal <;>
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
  refine .call (leftSplitOccurrence splitter) ?_ (by simp) ?_
  · intro input _
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
        aggregateBody, Composition.LeafwiseInterface.aggregateWiring,
        Composition.LeafwiseInterface.aggregateSplitterInputSource,
        Composition.LeafwiseInterface.aggregateContext,
        Composition.LeafwiseInterface.aggregateInstances, interface,
        Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput]
  · refine .call (rightSplitOccurrence splitter) ?_ ?_ ?_
    · intro input _
      cases splitter <;> cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
          aggregateBody, Composition.LeafwiseInterface.aggregateWiring,
          Composition.LeafwiseInterface.aggregateSplitterInputSource,
          Composition.LeafwiseInterface.aggregateContext,
          Composition.LeafwiseInterface.aggregateInstances, interface,
          Composition.LeafwiseInterface.inputType, EndpointContext.moduleInput]
    · intro member
      simp only [List.mem_singleton] at member
      have childEqual := congrArg
        Contracts.Cycle.Certification.Layer.RuleOccurrence.child member
      have inputEqual : Input.right = Input.left := by injection childEqual
      cases inputEqual
    · exact aggregateAfterSplitsSchedule splitter

def aggregateStateSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  .done (by
    intro child input member
    cases child with
    | splitter recursiveInput =>
        cases recursiveInput <;>
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

omit gate in
theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  cases child with
  | splitter recursiveInput =>
      cases recursiveInput <;> change Composition.SignalComponentRule at rule <;>
        cases rule
      · change leftSplitOccurrence splitter ∈
          (aggregateOutputSchedule splitter).finalAvailability
        unfold aggregateOutputSchedule
        change leftSplitOccurrence splitter ∈
          (aggregateAfterSplitsSchedule splitter).finalAvailability
        unfold aggregateAfterSplitsSchedule
        rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
        change leftSplitOccurrence splitter ∈
          combineOccurrence splitter :: (componentSchedule splitter).finalAvailability
        exact List.mem_cons_of_mem (combineOccurrence splitter)
          ((componentSchedule splitter).finished.1
            (leftSplitOccurrence splitter) (by simp))
      · change rightSplitOccurrence splitter ∈
          (aggregateOutputSchedule splitter).finalAvailability
        unfold aggregateOutputSchedule
        change rightSplitOccurrence splitter ∈
          (aggregateAfterSplitsSchedule splitter).finalAvailability
        unfold aggregateAfterSplitsSchedule
        rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
        change rightSplitOccurrence splitter ∈
          combineOccurrence splitter :: (componentSchedule splitter).finalAvailability
        exact List.mem_cons_of_mem (combineOccurrence splitter)
          ((componentSchedule splitter).finished.1
            (rightSplitOccurrence splitter) (by simp))
  | component component =>
      change Rule at rule
      cases rule
      change componentOccurrence splitter component ∈
        (aggregateOutputSchedule splitter).finalAvailability
      unfold aggregateOutputSchedule
      change componentOccurrence splitter component ∈
        (aggregateAfterSplitsSchedule splitter).finalAvailability
      unfold aggregateAfterSplitsSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      change componentOccurrence splitter component ∈
        combineOccurrence splitter :: (componentSchedule splitter).finalAvailability
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
        (aggregateAfterSplitsSchedule splitter).finalAvailability
      unfold aggregateAfterSplitsSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_self

def leftSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .left)

def rightSplitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) :
    splitter.ports.inputs.Values := splitter.inputValues (inputs .right)

omit gate in
@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = operation.apply signalType
        (inputs .left) (inputs .right) := by
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

omit gate in
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
        cases recursiveInput <;> change Subsingleton emptySignalMap.Values <;>
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
  have leftSplitOutputs : (childProposals (.splitter .left)).outputs =
      splitter.outputValues (leftSplitterInputs splitter inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (.splitter .left)).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure))
        inputs childProposals (.splitter .left) = leftSplitterInputs splitter inputs := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have rightSplitOutputs :
      (childProposals ((.splitter .right))).outputs =
        splitter.outputValues (rightSplitterInputs splitter inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (.splitter .right)).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure))
        inputs childProposals (.splitter .right) = rightSplitterInputs splitter inputs := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have componentOutputs : ∀ component,
      (childProposals ((.component component))).outputs .result =
        operation.apply (splitter.ports.outputs.signalType component)
          (splitter.outputValues (leftSplitterInputs splitter inputs) component)
          (splitter.outputValues (rightSplitterInputs splitter inputs) component) := by
    intro component
    have evaluates := (childMatch (.component component)).1
    have holds := evaluates.1 Rule.apply
    change (outputRule (splitter.ports.outputs.signalType component)).Holds
      _ _ _ at holds
    rw [outputRule_holds_iff] at holds
    have leftInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          ((.component component))) .left =
      splitter.outputValues (leftSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          ((.component component))) .right =
      splitter.outputValues (rightSplitterInputs splitter inputs) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact holds.trans (by rw [leftInput, rightInput])
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
      operation.apply splitter.aggregateType (inputs .left) (inputs .right)
    cases splitter with
    | vector length element =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs .value at boundaryResult
        rw [boundaryResult, congrFun combineOutputs .value]
        change (fun component =>
          (childProposals (.component component)).outputs .result) = _
        funext component
        exact (componentOutputs component).trans
          (congrFun (operation.split_apply (.vector length element)
            (inputs .left) (inputs .right)) component).symm
    | tuple fields =>
        have boundaryResult := boundary .result
        change outputs .result =
          (childProposals (.combiner .result)).outputs .value at boundaryResult
        rw [boundaryResult, congrFun combineOutputs .value]
        change fields.assemble (fun component =>
          (childProposals (.component component)).outputs .result) = _
        rw [← (SignalSplitter.tuple fields).combine_split
          (operation.apply (.tuple fields) (inputs .left) (inputs .right))]
        apply congrArg fields.assemble
        funext component
        exact (componentOutputs component).trans
          (congrFun (operation.split_apply (.tuple fields)
            (inputs .left) (inputs .right)) component).symm
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

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

omit gate in
/-- Contract-facing result law for the generic binary operation. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = operation.apply signalType
      (inputs .left) (inputs .right) :=
  (outputRule_holds_iff signalType inputs state outputs).mp (evaluates.1 .apply)

end Construction

end Silean.Composition.BinaryLeafwise
