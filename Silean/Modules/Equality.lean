import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.All
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Eq
import Silean.Composition.SignalLogic

namespace Silean.Modules.Equality

open Silean

/-! Generic structural equality. Aggregate values are compared recursively and
the component results are reduced with AND. -/

/-! ## Interface and exact behavior -/

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
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons .bit .nil } where
  readsInputs := ((inputMap signalType).select .right).prepend .left
  writesOutputs := outputMap.select .result
  target | (left, (right, ())), _ => (signalType.equal left right, ())

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.equal (inputs .left) (inputs .right) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem output_eq_true_iff_of_holds (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (holds : (outputRule signalType).Holds inputs state outputs) :
    outputs .result = true ↔ inputs .left = inputs .right := by
  rw [(outputRule_holds_iff signalType inputs state outputs).mp holds]
  exact signalType.equal_eq_true_iff _ _

/-! ## Hardware structure

The bit case is a transparent wrapper around the closed equality
primitive. -/

inductive BitInstance
  /-- The one-bit equality primitive. -/
  | gate
deriving Enumeration

@[reducible] def bitInstances : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.eq.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instancePorts where
  -- The primitive result is the module result.
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  -- Both operands feed the equality primitive.
  instanceInput
    | .gate, .left => bitContext.moduleInput .left
    | .gate, .right => bitContext.moduleInput .right

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩

@[reducible] def bitChildContracts : Contracts.Cycle.ChildCycleContracts bitBody
  | .gate => Primitives.eqCycleContract

@[reducible] def bitStructuralChildren :
    (child : bitInstances.Name) → ModuleStructure (bitInstances.ports child)
  | .gate => .primitive Primitives.eq

@[reducible] noncomputable def bitCertifiedChildren :
    (child : bitInstances.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts child)
  | .gate => ⟨.primitive Primitives.eq, Primitives.eqCertified.certification⟩

def bitModuleStructure : ModuleStructure (ports .bit) :=
  .composite bitBody bitStructuralChildren

abbrev bitOccurrence : Contracts.Cycle.Certification.Layer.RuleOccurrence
    bitBody bitChildContracts :=
  ⟨.gate, Primitives.EqRule.apply⟩

def bitOutputSchedule : Contracts.Cycle.Certification.Layer.OutputSchedule
    bitBody bitChildContracts
    (cycleContract .bit) .apply :=
  .call bitOccurrence
    (by
      intro input member
      cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
          bitBody, bitWiring, bitContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output _
      cases output
      exact ⟨Primitives.EqRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

def bitStateSchedule : Contracts.Cycle.Certification.Layer.StateSchedule
    bitBody bitChildContracts :=
  .done (by
    intro child input member
    cases child
    simp [bitChildContracts, Primitives.eqCycleContract,
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
  change Primitives.EqRule at rule
  cases rule
  refine ⟨.apply, ?_⟩
  change bitOccurrence ∈ bitOutputSchedule.finalAvailability
  simp [bitOutputSchedule,
    Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

def bitGateInputs (inputs : (ports .bit).inputs.Values) :
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

private theorem bitImplements : Contracts.Cycle.Implements
    (bitCertificationStructure layerChildren) (cycleContract .bit)
    (bitStateCorresponds layerChildren) := by
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
    rw [outputRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    have boundary := satisfies.1
    have gateInputs : ProposedValues.childInputs bitBody
        ((fun name => (layerChildren name).moduleStructure)) inputs children .gate =
          bitGateInputs inputs := by funext port; cases port <;> rfl
    have gateEquation := gateEvaluates.1 Primitives.EqRule.apply
    change (Primitives.eqOutputRule).Holds _ _ _ at gateEquation
    rw [Primitives.eqOutputRule_holds_iff] at gateEquation
    rw [gateInputs] at gateEquation
    exact (boundary .result).trans (gateEquation.trans (by
      simp [SignalType.equal, bitGateInputs]))
  · rfl

end BitLayerCertification

noncomputable opaque bitCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer bitBody bitChildContracts
      (cycleContract .bit) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    bitRuleSchedules bitCoversChildren bitStateCorresponds
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

/-! Aggregate equality has two operand splitters, one recursive equality
instance per
immediate component, and one `All` child consuming the family of results. -/

abbrev AggregateInstance (splitter : Composition.SignalSplitter) :=
  Sum Input (Sum splitter.ports.outputs.Label PUnit)

@[reducible] def aggregateInstanceEnumeration (splitter : Composition.SignalSplitter) :
    Enumeration (AggregateInstance splitter) :=
  Enumeration.sum inferInstance
    (Enumeration.sum splitter.ports.outputs.labels Enumeration.punit)

private abbrev splitInstance (input : Input) : AggregateInstance splitter := .inl input
private abbrev componentInstance (component : splitter.ports.outputs.Label) :
    AggregateInstance splitter := .inr (.inl component)
private abbrev allInstance : AggregateInstance splitter := .inr (.inr .unit)

def componentCount (splitter : Composition.SignalSplitter) : Nat :=
  splitter.ports.outputs.labels.values.length

@[reducible] def aggregateInstances (splitter : Composition.SignalSplitter) : InstancePorts where
  Key := AggregateInstance splitter
  keys := aggregateInstanceEnumeration splitter
  value
    | .inl _ => splitter.ports
    | .inr (.inl component) =>
        ports (splitter.ports.outputs.signalType component)
    | .inr (.inr _) => All.ports (componentCount splitter)

@[reducible] def aggregateContext (splitter : Composition.SignalSplitter) : EndpointContext where
  ports := ports splitter.aggregateType
  instancePorts := aggregateInstances splitter

private def componentAt (splitter : Composition.SignalSplitter)
    (index : Fin (componentCount splitter)) : splitter.ports.outputs.Label :=
  splitter.ports.outputs.labels.values[index.val]'(by
    simp [componentCount])

@[simp] theorem componentAt_ordinal (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    componentAt splitter (splitter.ports.outputs.labels.ordinal component) =
      component := by
  exact (splitter.ports.outputs.labels.locate component).get_eq

theorem all_components_equal_iff (splitter : Composition.SignalSplitter)
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

def aggregateWiring (splitter : Composition.SignalSplitter) :
    Wiring (aggregateContext splitter).ports (aggregateContext splitter).instancePorts where
  moduleOutput
    -- The reduction result is the aggregate equality result.
    | .result => (aggregateContext splitter).instanceOutput allInstance .output
  instanceInput
    -- Split the left and right operands into matching components.
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
    -- Feed every component comparison into the `All` reduction.
    | .inr (.inr _), input =>
        (aggregateContext splitter).instanceOutput
          (componentInstance (componentAt splitter
            (All.inputIndex (componentCount splitter) input))) .result

@[reducible] def aggregateBody (splitter : Composition.SignalSplitter) : ModuleBody :=
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
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType) (cycleContract signalType)

/-- Recursive equality and every module below it have concrete structure. -/
def Implementation.certified (implementation : Implementation signalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

@[reducible] def aggregateChildContracts (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.ChildCycleContracts (aggregateBody splitter)
  | .inl _ => splitter.cycleContract
  | .inr (.inl component) =>
      cycleContract (splitter.ports.outputs.signalType component)
  | .inr (.inr _) => All.cycleContract (componentCount splitter)

def splitterInputs (splitter : Composition.SignalSplitter)
    (inputs : (ports splitter.aggregateType).inputs.Values) (which : Input) :
    splitter.ports.inputs.Values := match which with
  | .left => splitter.inputValues (inputs .left)
  | .right => splitter.inputValues (inputs .right)

abbrev leftSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨splitInstance .left, Composition.SignalComponentRule.apply⟩

abbrev rightSplitOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨splitInstance .right, Composition.SignalComponentRule.apply⟩

abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨componentInstance component, Rule.apply⟩

abbrev allOccurrence (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter) :=
  ⟨allInstance, All.Rule.apply⟩

@[simp] theorem leftSplitOccurrence_writes (splitter : Composition.SignalSplitter) :
    (leftSplitOccurrence splitter).writes =
      splitter.ports.outputs.labels.values := by
  change splitter.ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]

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
          [rightSplitOccurrence splitter,
            leftSplitOccurrence splitter] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [rightSplitOccurrence splitter,
            leftSplitOccurrence splitter] ∨
          ∃ component, called = componentOccurrence splitter component)
      [rightSplitOccurrence splitter,
        leftSplitOccurrence splitter] :=
  Contracts.Cycle.Certification.Layer.Schedule.callFamilyAfter
    [rightSplitOccurrence splitter,
      leftSplitOccurrence splitter]
    splitter.ports.outputs.labels
    (componentOccurrence splitter)
    (by
      intro left right equal
      have childEqual := congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal
      exact Sum.inl.inj (Sum.inr.inj childEqual))
    (by
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro component input _
      cases input with
      | left =>
          refine ⟨Composition.SignalComponentRule.apply, by simp, ?_⟩
          change component ∈ (leftSplitOccurrence splitter).writes
          rw [leftSplitOccurrence_writes]
          exact ListIndex.get_eq
            (splitter.ports.outputs.labels.locate component) ▸ List.get_mem _ _
      | right =>
          refine ⟨Composition.SignalComponentRule.apply, by simp, ?_⟩
          change component ∈ (rightSplitOccurrence splitter).writes
          rw [rightSplitOccurrence_writes]
          exact ListIndex.get_eq
            (splitter.ports.outputs.labels.locate component) ▸ List.get_mem _ _)

noncomputable def afterComponentsSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter)
      (fun input => input ∈ (outputRule splitter.aggregateType).readsInputs.labels)
      (Contracts.Cycle.Certification.Layer.BoundaryReady (aggregateBody splitter)
        (aggregateChildContracts splitter)
        (outputRule splitter.aggregateType).writesOutputs.labels
        (fun input => input ∈
          (outputRule splitter.aggregateType).readsInputs.labels))
      [rightSplitOccurrence splitter,
        leftSplitOccurrence splitter] := by
  apply (componentSchedule splitter).append
  refine .call (allOccurrence splitter) ?_ ?_ (.done ?_)
  · intro input _
    let component := componentAt splitter
      (All.inputIndex (componentCount splitter) input)
    refine ⟨Rule.apply,
      (componentSchedule splitter).finished.2.1 component, ?_⟩
    change Output.result ∈
      (outputRule (splitter.ports.outputs.signalType component)).writesOutputs.labels
    simp [outputRule, SignalMap.select, SignalSelection.labels]
  · intro present
    rcases (componentSchedule splitter).finished.2.2 _ present with
      atStart | fromComponent
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at atStart
      rcases atStart with equal | equal <;>
        have childEqual := congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal <;>
        cases childEqual
    · rcases fromComponent with ⟨component, equal⟩
      have childEqual := congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal
      cases childEqual
  · intro output _
    cases output
    exact ⟨All.Rule.apply, by simp, by
      change Primitives.SingleOutput.output ∈
        (All.outputRule (componentCount splitter)).writesOutputs.labels
      simp [All.outputRule, SignalMap.select, SignalSelection.labels]⟩

noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.OutputSchedule (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType)
      .apply := by
  refine .call (leftSplitOccurrence splitter) ?_ (by simp) ?_
  · intro input _
    cases splitter <;> cases input <;>
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable, aggregateBody,
        aggregateWiring, aggregateContext, EndpointContext.moduleInput]
  · refine .call (rightSplitOccurrence splitter) ?_
      (by
        intro member
        have equal := List.mem_singleton.mp member
        have childEqual := congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal
        have inputEqual : Input.right = Input.left := by injection childEqual
        cases inputEqual) ?_
    · intro input _
      cases splitter <;> cases input <;>
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable, aggregateBody,
          aggregateWiring, aggregateContext, EndpointContext.moduleInput]
    · exact afterComponentsSchedule splitter

def aggregateStateSchedule (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.StateSchedule (aggregateBody splitter)
      (aggregateChildContracts splitter) :=
  .done (by
    intro child input member
    rcases child with which | componentOrAll
    · cases which <;>
        simp [aggregateChildContracts,
          Composition.SignalSplitter.cycleContract, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    · rcases componentOrAll with component | allTag
      · simp [aggregateChildContracts, cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member
      · cases allTag
        simp [aggregateChildContracts, All.cycleContract,
          Contracts.Cycle.CycleStateRule.empty] at member
        change input ∈ SignalSelection.nil.labels at member
        exact nomatch member)

noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter) :
    Contracts.Cycle.Certification.Layer.RuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter) (cycleContract splitter.aggregateType) where
  output | .apply => aggregateOutputSchedule splitter
  state := aggregateStateSchedule splitter

theorem leftSplit_mem_outputSchedule (splitter : Composition.SignalSplitter) :
    leftSplitOccurrence splitter ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  unfold aggregateOutputSchedule
  change leftSplitOccurrence splitter ∈
    (afterComponentsSchedule splitter).finalAvailability
  unfold afterComponentsSchedule
  simp only [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter).finished.1 _ (by simp))

theorem rightSplit_mem_outputSchedule (splitter : Composition.SignalSplitter) :
    rightSplitOccurrence splitter ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  unfold aggregateOutputSchedule
  change rightSplitOccurrence splitter ∈
    (afterComponentsSchedule splitter).finalAvailability
  unfold afterComponentsSchedule
  simp only [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter).finished.1 _ (by simp))

theorem component_mem_outputSchedule (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter component ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  unfold aggregateOutputSchedule
  change componentOccurrence splitter component ∈
    (afterComponentsSchedule splitter).finalAvailability
  unfold afterComponentsSchedule
  simp only [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter).finished.2.1 component)

theorem all_mem_outputSchedule (splitter : Composition.SignalSplitter) :
    allOccurrence splitter ∈
      (aggregateOutputSchedule splitter).finalAvailability := by
  unfold aggregateOutputSchedule
  change allOccurrence splitter ∈
    (afterComponentsSchedule splitter).finalAvailability
  unfold afterComponentsSchedule
  simp only [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
  exact List.mem_cons_self

theorem aggregateCoversChildren (splitter : Composition.SignalSplitter) :
    (aggregateRuleSchedules splitter).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  rcases child with which | componentOrAll
  · cases which with
    | left =>
        change Composition.SignalComponentRule at rule
        cases rule
        exact leftSplit_mem_outputSchedule splitter
    | right =>
        change Composition.SignalComponentRule at rule
        cases rule
        exact rightSplit_mem_outputSchedule splitter
  · rcases componentOrAll with component | allTag
    · change Rule at rule
      cases rule
      exact component_mem_outputSchedule splitter component
    · cases allTag
      change All.Rule at rule
      cases rule
      exact all_mem_outputSchedule splitter

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
    Contracts.Cycle.Implements
      (aggregateCertificationStructure splitter layerChildren)
      (cycleContract splitter.aggregateType)
      (aggregateStateCorresponds splitter layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton (child : AggregateInstance splitter) :
      Subsingleton
        ((aggregateChildContracts splitter child).state.Values) := by
    rcases child with which | componentOrAll
    · cases which <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    · rcases componentOrAll with component | allTag
      · change Subsingleton emptySignalMap.Values; infer_instance
      · cases allTag; change Subsingleton emptySignalMap.Values; infer_instance
  have childMatch (child : AggregateInstance splitter) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
        proposal satisfies child (by rcases child with (_ | _) | (_ | _) <;> exact SignalMap.emptyValues)
  rcases proposal with ⟨outputs, childProposals⟩
  have boundary := satisfies.1
  have leftSplitOutputs : (childProposals (splitInstance .left)).outputs =
      splitter.outputValues (splitterInputs splitter inputs .left) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (splitInstance .left)).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (splitInstance .left) = splitterInputs splitter inputs .left := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have rightSplitOutputs : (childProposals (splitInstance .right)).outputs =
      splitter.outputValues (splitterInputs splitter inputs .right) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff splitter _ _ _).mp
      ((childMatch (splitInstance .right)).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (aggregateBody splitter)
        ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (splitInstance .right) = splitterInputs splitter inputs .right := by
      cases splitter <;> funext port <;> cases port <;> rfl
    rw [inputsEqual] at holds
    exact holds
  have componentOutputs : ∀ component,
      (childProposals (componentInstance component)).outputs .result =
        (splitter.ports.outputs.signalType component).equal
          (splitter.outputValues (splitterInputs splitter inputs .left) component)
          (splitter.outputValues (splitterInputs splitter inputs .right) component) := by
    intro component
    have evaluates := (childMatch (componentInstance component)).1
    have equation := evaluates.1 Rule.apply
    change (outputRule (splitter.ports.outputs.signalType component)).Holds _ _ _ at equation
    rw [outputRule_holds_iff] at equation
    have leftInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (componentInstance component)) .left =
        splitter.outputValues (splitterInputs splitter inputs .left) component := by
      cases splitter <;> exact congrFun leftSplitOutputs component
    have rightInput :
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (componentInstance component)) .right =
        splitter.outputValues (splitterInputs splitter inputs .right) component := by
      cases splitter <;> exact congrFun rightSplitOutputs component
    exact equation.trans (by rw [leftInput, rightInput])
  have allEvaluates := (childMatch allInstance).1
  have allHolds := allEvaluates.1 All.Rule.apply
  change (All.outputRule (componentCount splitter)).Holds
    (ProposedValues.childInputs (aggregateBody splitter)
      ((fun name => (layerChildren name).moduleStructure)) inputs childProposals allInstance)
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
        ((fun name => (layerChildren name).moduleStructure)) inputs childProposals allInstance)
      SignalMap.emptyValues (childProposals allInstance).outputs allHolds
    refine allCharacterization.trans ?_
    rw [splitter.aggregateType.equal_eq_true_iff]
    rw [← all_components_equal_iff splitter]
    constructor
    · intro every component
      have result := every (splitter.ports.outputs.labels.ordinal component)
      rw [show ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals allInstance
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
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals allInstance
          (All.input (componentCount splitter) index) =
          (childProposals (componentInstance component)).outputs .result by
        simp [ProposedValues.childInputs, aggregateBody, aggregateWiring,
          EndpointContext.instanceOutput, SignalSource.value]
        rw [All.inputIndex_input]]
      rw [componentOutputs component]
      apply (splitter.ports.outputs.signalType component).equal_eq_true_iff _ _ |>.mpr
      exact every component
  · rfl

end AggregateLayerCertification

noncomputable opaque aggregateCertifiedLayer (splitter : Composition.SignalSplitter) :
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
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := (implementation signalType).certified

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType := rfl

theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

/-- Contract-facing equality result law. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = signalType.equal (inputs .left) (inputs .right) :=
  (outputRule_holds_iff signalType inputs state outputs).mp (evaluates.1 .apply)

end Silean.Modules.Equality

namespace Silean.Modules.Equality.Naming

open Silean Silean.Naming

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
      unfold Modules.Equality.bitModuleStructure
      exact .composite ⟨"equality", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean.Naming.Primitive.eq)
  | .vector length element, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : Composition.SignalSplitter := .vector length element
      exact .composite ⟨"equality", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => indexedComponent splitter.ports.outputs component
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inr (.inl component) =>
              namingWith element (typeNaming.component component)
          | .inr (.inr _) => All.Naming.naming (Modules.Equality.componentCount splitter))
  | .tuple fields, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"equality", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => indexedComponent splitter.ports.outputs component
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
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

end Silean.Modules.Equality.Naming
