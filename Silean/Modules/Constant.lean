import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Constant

open Silean

/-! A constant source for any signal type, recursively assembled from one-bit
constant primitives. -/

abbrev Output := Primitives.SingleOutput

@[reducible] private def interface : Composition.LeafwiseInterface where
  Input := NoSignal
  inputs := inferInstance
  RecursiveInput := NoSignal
  recursiveInputs := inferInstance
  FixedInput := NoSignal
  fixedInputs := inferInstance
  inputLayout := {
    classify := fun impossible => nomatch impossible
    label := fun
      | .inl impossible => nomatch impossible
      | .inr impossible => nomatch impossible
    classify_label := by intro part; cases part <;> rename_i impossible <;>
      exact nomatch impossible
    label_classify := by intro impossible; exact nomatch impossible }
  fixedInputType := fun impossible => nomatch impossible
  Output := Output
  outputs := inferInstance
  State := NoSignal
  states := inferInstance

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  interface.ports signalType

private abbrev Rule := Primitives.ConstantRule

def outputRule (signalType : SignalType) (value : signalType.Denote) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (ports signalType).outputs.select .output
  target | (), _ => (value, ())

@[reducible] def cycleContract (signalType : SignalType)
    (value : signalType.Denote) : Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType value⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (value : signalType.Denote) (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values) (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType value).Holds inputs state outputs ↔
      outputs .output = value := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

/-! ## Hardware structure -/

private inductive BitInstance
  /-- The one-bit constant primitive. -/
  | source
deriving Enumeration

@[reducible] private def bitInstances (value : Bool) : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .source => (Primitives.constant value).ports

@[reducible] private def bitContext (value : Bool) : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances value

private def bitWiring (value : Bool) :
    Wiring (bitContext value).ports (bitContext value).instancePorts where
  -- The primitive directly drives the module output and has no inputs.
  moduleOutput | .output => (bitContext value).instanceOutput .source .output
  instanceInput | .source, impossible => nomatch impossible

@[reducible] private def bitBody (value : Bool) : ModuleBody :=
  ⟨bitContext value, bitWiring value⟩

@[reducible] private def bitChildContracts (value : Bool) :
    Contracts.Cycle.ChildCycleContracts (bitBody value)
  | .source => Primitives.constantCycleContract value

@[reducible] private def bitStructuralChildren (value : Bool) :
    (child : (bitInstances value).Name) →
      ModuleStructure ((bitInstances value).ports child)
  | .source => .primitive (Primitives.constant value)

@[reducible] private noncomputable def bitCertifiedChildren (value : Bool) :
    (child : (bitInstances value).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts value child)
  | .source =>
      ⟨.primitive (Primitives.constant value),
        (Primitives.constantCertified value).certification⟩

private def bitModuleStructure (value : Bool) : ModuleStructure (ports .bit) :=
  .composite (bitBody value) (bitStructuralChildren value)

def moduleStructure : (signalType : SignalType) → signalType.Denote →
    ModuleStructure (ports signalType)
  | .bit, value => bitModuleStructure value
  | .vector length element, value =>
      let splitter : Composition.SignalSplitter := .vector length element
      .composite (interface.aggregateBody splitter) fun
        | .splitter impossible => nomatch impossible
        | .component component => moduleStructure element (value component)
        | .combiner _ => .combiner splitter.combiner
  | .tuple fields, value =>
      let splitter : Composition.SignalSplitter := .tuple fields
      .composite (interface.aggregateBody splitter) fun
        | .splitter impossible => nomatch impossible
        | .component component =>
            moduleStructure (fields.typeAt component) (fields.get value component)
        | .combiner _ => .combiner splitter.combiner
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

private theorem moduleStructure_bit (value : SignalType.bit.Denote) :
    moduleStructure .bit value = bitModuleStructure value := by
  rw [moduleStructure.eq_def]

abbrev Implementation (signalType : SignalType) (value : signalType.Denote) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType value)
    (cycleContract signalType value)

def Implementation.certified
    (implementation : Implementation signalType value) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

private abbrev bitOccurrence (value : Bool) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (bitBody value) (bitChildContracts value) :=
  ⟨.source, Primitives.ConstantRule.apply⟩

private def bitOutputSchedule (value : Bool) :
    Contracts.Cycle.Certification.Layer.OutputSchedule
      (bitBody value) (bitChildContracts value)
      (cycleContract .bit value) .apply :=
  .call (bitOccurrence value)
    (by intro input member; exact nomatch input)
    (by simp)
    (.done (by
      intro outputName member
      cases outputName
      exact ⟨Primitives.ConstantRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

private def bitStateSchedule (value : Bool) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (bitBody value) (bitChildContracts value) :=
  .done (by
    intro child input member
    cases child
    simp [bitChildContracts,
      Primitives.constantCycleContract, Contracts.Cycle.CycleStateRule.empty,
      SignalSelection.labels] at member)

private def bitRuleSchedules (value : Bool) :
    Contracts.Cycle.Certification.Layer.RuleSchedules
      (bitBody value) (bitChildContracts value)
      (cycleContract .bit value) where
  output | .apply => bitOutputSchedule value
  state := bitStateSchedule value

private theorem bitCoversChildren (value : Bool) :
    (bitRuleSchedules value).CoversChildren := by
  intro child rule
  right
  cases child
  change Primitives.ConstantRule at rule
  cases rule
  refine ⟨.apply, ?_⟩
  change bitOccurrence value ∈ (bitOutputSchedule value).finalAvailability
  simp [bitOutputSchedule,
    Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

section BitLayerCertification

variable (value : Bool)
  (layerChildren : (child : (bitInstances value).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts value child))

private abbrev bitCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (bitBody value) layerChildren

private def bitStateCorresponds (_ : emptySignalMap.Values)
    (_ : (bitCertificationStructure value layerChildren).State) : Prop := True

private theorem bitImplements :
    Contracts.Cycle.Implements
      (bitCertificationStructure value layerChildren) (cycleContract .bit value)
      (bitStateCorresponds value layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  letI : Subsingleton
      ((bitChildContracts value .source).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have sourceEvaluates :=
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal
        satisfies .source SignalMap.emptyValues).1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    have boundary := satisfies.1
    have sourceOutput : (children .source).outputs .output = value :=
      (Primitives.constantOutputRule_holds_iff value _ _ _).mp
        (sourceEvaluates.1 Primitives.ConstantRule.apply)
    exact (boundary .output).trans sourceOutput
  · rfl

end BitLayerCertification

noncomputable opaque bitCertifiedLayer (value : Bool) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (bitBody value)
      (bitChildContracts value) (cycleContract .bit value) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (bitRuleSchedules value) (bitCoversChildren value) (bitStateCorresponds value)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (bitImplements value)

noncomputable def bitCertifiedStructure (value : Bool) :
    Contracts.Cycle.ModuleCycleCertifiedStructure (cycleContract .bit value) :=
  (bitCertifiedLayer value).instantiate (bitCertifiedChildren value)

@[simp] theorem bitCertifiedStructure_moduleStructure (value : Bool) :
    (bitCertifiedStructure value).moduleStructure = bitModuleStructure value := by
  unfold bitCertifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    bitModuleStructure
  change ModuleStructure.composite (bitBody value) (fun child =>
    (bitCertifiedChildren value child).moduleStructure) =
      ModuleStructure.composite (bitBody value) (bitStructuralChildren value)
  congr

private noncomputable def bitImplementation (value : SignalType.bit.Denote) :
    Implementation .bit value :=
  (bitCertifiedStructure value).certification.transportStructure
    ((bitCertifiedStructure_moduleStructure value).trans
      (moduleStructure_bit value).symm)

@[reducible] private def aggregateBody (splitter : Composition.SignalSplitter) :=
  interface.aggregateBody splitter

@[reducible] private def componentValue (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (component : splitter.ports.outputs.Label) :
    (splitter.ports.outputs.signalType component).Denote :=
  splitter.outputValues (splitter.inputValues value) component

@[reducible] private def componentContracts (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (ports (splitter.ports.outputs.signalType component)) :=
  fun component => cycleContract _ (componentValue splitter value component)

@[reducible] private def aggregateChildContracts (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :=
  interface.aggregateChildContracts splitter (componentContracts splitter value)

private abbrev componentOccurrence (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (component : splitter.ports.outputs.Label) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter value) :=
  interface.componentOccurrence splitter (componentContracts splitter value)
    component Primitives.ConstantRule.apply

private abbrev combineOccurrence (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (aggregateBody splitter) (aggregateChildContracts splitter value) :=
  interface.combinerOccurrence splitter (componentContracts splitter value) .output

private noncomputable def componentSchedule (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.Certification.Layer.Schedule (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (fun input => input ∈ (outputRule splitter.aggregateType value).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter value component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [] ∨ ∃ component, called = componentOccurrence splitter value component)
      [] :=
  interface.callComponentsAfter splitter (componentContracts splitter value) []
    (fun _ => Primitives.ConstantRule.apply) (by simp)
    (by intro component input member; exact nomatch input)

private noncomputable def aggregateOutputSchedule (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.Certification.Layer.OutputSchedule (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (cycleContract splitter.aggregateType value) .apply := by
  apply (componentSchedule splitter value).append
  refine .call (combineOccurrence splitter value) ?_ ?_ (.done ?_)
  · intro input _
    cases splitter <;>
      exact ⟨Primitives.ConstantRule.apply,
        (componentSchedule _ value).finished.2.1 input,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
  · intro present
    rcases (componentSchedule splitter value).finished.2.2 _ present with
      atStart | ⟨component, equal⟩
    · simp at atStart
    · cases equal
  · intro outputName _
    cases outputName
    cases splitter <;>
      exact ⟨Composition.SignalComponentRule.apply, by simp,
        by change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]; simp⟩

private def aggregateStateSchedule (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (aggregateBody splitter) (aggregateChildContracts splitter value) :=
  .done (by
    intro child input member
    cases child with
    | splitter impossible => exact nomatch impossible
    | component component =>
        simp [aggregateChildContracts,
          Composition.LeafwiseInterface.aggregateChildContracts,
          componentContracts, cycleContract, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | combiner outputName =>
        cases outputName
        simp [aggregateChildContracts,
          Composition.LeafwiseInterface.aggregateChildContracts,
          Composition.SignalCombiner.cycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

private noncomputable def aggregateRuleSchedules (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (cycleContract splitter.aggregateType value) where
  output | .apply => aggregateOutputSchedule splitter value
  state := aggregateStateSchedule splitter value

private theorem aggregateCoversChildren (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    (aggregateRuleSchedules splitter value).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  cases child with
  | splitter impossible => exact nomatch impossible
  | component component =>
      change Rule at rule
      cases rule
      change componentOccurrence splitter value component ∈
        (aggregateOutputSchedule splitter value).finalAvailability
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_of_mem _
        ((componentSchedule splitter value).finished.2.1 component)
  | combiner outputName =>
      cases outputName
      change Composition.SignalComponentRule at rule
      cases rule
      change combineOccurrence splitter value ∈
        (aggregateOutputSchedule splitter value).finalAvailability
      unfold aggregateOutputSchedule
      rw [Contracts.Cycle.Certification.Layer.Schedule.finalAvailability_append]
      exact List.mem_cons_self

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (value : splitter.aggregateType.Denote)
  (layerChildren : (child : (aggregateBody splitter).context.instancePorts.Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (aggregateChildContracts splitter value child))

private abbrev aggregateCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (aggregateBody splitter) layerChildren

private def aggregateStateCorresponds (_ : emptySignalMap.Values)
    (_ : (aggregateCertificationStructure splitter value layerChildren).State) : Prop := True

private theorem aggregateImplements :
    Contracts.Cycle.Implements
      (aggregateCertificationStructure splitter value layerChildren)
      (cycleContract splitter.aggregateType value)
      (aggregateStateCorresponds splitter value layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton
      (child : (aggregateBody splitter).context.instancePorts.Name) :
      Subsingleton
        ((aggregateChildContracts splitter value child).state.Values) := by
    cases child with
    | splitter impossible => exact nomatch impossible
    | component component => change Subsingleton emptySignalMap.Values; infer_instance
    | combiner outputName => cases outputName; change Subsingleton emptySignalMap.Values; infer_instance
  have childMatch (child : (aggregateBody splitter).context.instancePorts.Name) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
        proposal satisfies child (by cases child <;> exact SignalMap.emptyValues)
  rcases proposal with ⟨outputs, childProposals⟩
  have boundary := satisfies.1
  have componentOutputs : ∀ component,
      (childProposals (.component component)).outputs .output =
        componentValue splitter value component := by
    intro component
    have evaluates := (childMatch (.component component)).1
    have holds := evaluates.1 Primitives.ConstantRule.apply
    change (outputRule _ (componentValue splitter value component)).Holds _ _ _ at holds
    exact (outputRule_holds_iff _ _ _ _ _).mp holds
  have combineOutputs : (childProposals (.combiner .output)).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          ((fun name => (layerChildren name).moduleStructure)) inputs childProposals
          (.combiner .output)) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff splitter.combiner _ _ _).mp
      ((childMatch (.combiner .output)).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .output = value
    cases splitter with
    | vector length element =>
        have boundaryOutput := boundary .output
        change outputs .output =
          (childProposals (.combiner .output)).outputs Composition.AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs Composition.AggregatePort.value]
        change (fun component =>
          (childProposals (.component component)).outputs .output) = value
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryOutput := boundary .output
        change outputs .output =
          (childProposals (.combiner .output)).outputs Composition.AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs Composition.AggregatePort.value]
        change fields.assemble (fun component =>
          (childProposals (.component component)).outputs .output) = value
        calc
          fields.assemble (fun component =>
              (childProposals (.component component)).outputs .output) =
              fields.assemble (fun component => fields.get value component) := by
                apply congrArg fields.assemble
                funext component
                exact componentOutputs component
          _ = value := fields.assemble_get value
  · funext state
    exact nomatch state

end AggregateLayerCertification

noncomputable opaque aggregateCertifiedLayer
    (splitter : Composition.SignalSplitter) (value : splitter.aggregateType.Denote) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (cycleContract splitter.aggregateType value) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (aggregateRuleSchedules splitter value) (aggregateCoversChildren splitter value)
    (aggregateStateCorresponds splitter value)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (aggregateImplements splitter value)

@[reducible] private noncomputable def aggregateCertifiedChildren
    (splitter : Composition.SignalSplitter) (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    (child : (aggregateBody splitter).context.instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter value child)
  | .splitter impossible => nomatch impossible
  | .component component =>
      ⟨moduleStructure _ (componentValue splitter value component), components component⟩
  | .combiner _ =>
      ⟨.combiner splitter.combiner, splitter.combiner.certified.certification⟩

private noncomputable def aggregateImplementation (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Implementation splitter.aggregateType value := by
  let instantiated := (aggregateCertifiedLayer splitter value).instantiate
    (aggregateCertifiedChildren splitter value components)
  have sameStructure : instantiated.moduleStructure =
      moduleStructure splitter.aggregateType value := by
    unfold instantiated Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    change ModuleStructure.composite (aggregateBody splitter)
      (fun child =>
        (aggregateCertifiedChildren splitter value components child).moduleStructure) =
          moduleStructure splitter.aggregateType value
    cases splitter with
    | vector length element =>
        rw [moduleStructure]
        congr
        funext child
        cases child with
        | splitter impossible => exact nomatch impossible
        | component component => rfl
        | combiner outputName => cases outputName; rfl
    | tuple fields =>
        rw [moduleStructure]
        congr
        funext child
        cases child with
        | splitter impossible => exact nomatch impossible
        | component component => rfl
        | combiner outputName => cases outputName; rfl
  exact instantiated.certification.transportStructure sameStructure

private noncomputable def implementationDefinition :
    (signalType : SignalType) → (value : signalType.Denote) →
      Implementation signalType value
  | .bit, value => bitImplementation value
  | .vector length element, value =>
      aggregateImplementation (.vector length element) value fun component =>
        implementationDefinition element (value component)
  | .tuple fields, value =>
      aggregateImplementation (.tuple fields) value fun component =>
        implementationDefinition (fields.typeAt component)
          (fields.get value component)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

private noncomputable opaque implementation (signalType : SignalType)
    (value : signalType.Denote) : Implementation signalType value :=
  implementationDefinition signalType value

noncomputable def certified (signalType : SignalType)
    (value : signalType.Denote) : Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (implementation signalType value).certified

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).moduleStructure = moduleStructure signalType value :=
  rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).cycleContract = cycleContract signalType value :=
  rfl

/-- Contract-facing constant result law. -/
theorem output_of_evaluatesTo (signalType : SignalType) (value : signalType.Denote)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType value).EvaluatesTo inputs state outputs nextState) :
    outputs .output = value :=
  (outputRule_holds_iff signalType value inputs state outputs).mp (evaluates.1 .apply)

end Silean.Modules.Constant

namespace Silean.Modules.Constant.Naming

open Silean Silean.Naming

private def bitParameter (value : SignalType.bit.Denote) : Nat :=
  match value with
  | false => 0
  | true => 1

mutual
  private def valueParameters : (signalType : SignalType) →
      signalType.Denote → List ModuleParameter
    | .bit, value => [.natural (bitParameter value)]
    | .vector _ element, value =>
        (List.ofFn value).flatMap (valueParameters element)
    | .tuple fields, value => fieldValueParameters fields value

  private def fieldValueParameters : (fields : SignalTypes) →
      fields.Denote → List ModuleParameter
    | .nil, () => []
    | .cons head tail, (headValue, tailValue) =>
      valueParameters head headValue ++ fieldValueParameters tail tailValue
end

def parameters (signalType : SignalType) (value : signalType.Denote) :
    List ModuleParameter :=
  valueParameters signalType value

private def indexedComponent (signals : SignalMap) (component : signals.Label) :
    SourceName :=
  .scoped "constant" ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Constant.ports signalType) where
  inputs := ⟨fun impossible => nomatch impossible⟩
  outputs := ⟨fun | .output => "value"⟩
  outputTypes := fun | .output => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Constant.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → (value : signalType.Denote) →
    SignalTypeNaming signalType →
      ModuleNaming (Modules.Constant.moduleStructure signalType value)
  | .bit, value, typeNaming => by
      rw [Modules.Constant.moduleStructure.eq_def]
      exact .composite
        ⟨"constant", "bit", [.natural (bitParameter value)]⟩
        (portsWithNaming .bit typeNaming)
        (fun | .source => "source")
        (fun | .source => Silean.Naming.Primitive.constant value)
  | .vector length element, value, typeNaming => by
      rw [Modules.Constant.moduleStructure.eq_def]
      let splitter : Composition.SignalSplitter := .vector length element
      exact .composite
        ⟨"constant", "structural",
          .shape splitter.aggregateType :: valueParameters splitter.aggregateType value⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter impossible => nomatch impossible
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .output => "combine")
        (fun
          | .splitter impossible => nomatch impossible
          | .component component =>
              namingWith element (value component) (typeNaming.component component)
          | .combiner .output =>
              Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner
                typeNaming)
  | .tuple fields, value, typeNaming => by
      rw [Modules.Constant.moduleStructure.eq_def]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite
        ⟨"constant", "structural",
          .shape splitter.aggregateType :: valueParameters splitter.aggregateType value⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter impossible => nomatch impossible
          | .component component => indexedComponent splitter.ports.outputs component
          | .combiner .output => "combine")
        (fun
          | .splitter impossible => nomatch impossible
          | .component component =>
              namingWith (fields.typeAt component) (fields.get value component)
                (typeNaming.component component)
          | .combiner .output =>
              Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner
                typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) (value : signalType.Denote) :
    ModuleNaming (Modules.Constant.moduleStructure signalType value) :=
  namingWith signalType value (.positional signalType)

end Silean.Modules.Constant.Naming
