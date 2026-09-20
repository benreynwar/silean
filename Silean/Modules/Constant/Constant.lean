import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Constant
import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleCertification

namespace Silean.Modules.Constant

open Silean
open Contracts.Cycle.Certification.Layer

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
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap where
  readsInputs := .empty (ports signalType).inputs
  writesOutputs := .all (ports signalType).outputs
  target _ _ := fun | .output => value

@[reducible] def cycleContract (signalType : SignalType)
    (value : signalType.Denote) : Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule signalType value
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (value : signalType.Denote) (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values) (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType value).Holds inputs state outputs ↔
      outputs .output = value := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

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

def moduleStructure : (signalType : SignalType) →
    signalType.Denote → ModuleStructure (ports signalType)
  | .bit, value => bitModuleStructure value
  | .vector length elementType, value =>
      let splitter : Composition.SignalSplitter := .vector length elementType
      .composite (interface.aggregateBody splitter) fun
        | .splitter impossible => nomatch impossible
        | .component component => moduleStructure elementType (value component)
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
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

private theorem moduleStructure_bit (value : SignalType.bit.Denote) :
    moduleStructure .bit value = bitModuleStructure value := by
  rw [moduleStructure.eq_def]

abbrev Implementation (signalType : SignalType) (value : signalType.Denote) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType value)
    (cycleContract signalType value)

def Implementation.certified
    {signalType : SignalType} {value : signalType.Denote}
    (implementation : Implementation signalType value) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) := implementation.bundle

private abbrev bitOccurrence (value : Bool) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (bitBody value) (bitChildContracts value) :=
  ⟨.source, Primitives.ConstantRule.apply⟩

private def bitScheduleOrders (value : Bool) :
    ScheduleDerivation.RuleScheduleOrders (bitBody value)
      (bitChildContracts value) (cycleContract .bit value) where
  output | .apply => [bitOccurrence value]
  state := []

private def bitDerivedRuleSchedules (value : Bool) :
    ScheduleDerivation.DerivedRuleSchedules (bitBody value)
      (bitChildContracts value) (cycleContract .bit value) := by
  derive_rule_schedules (bitScheduleOrders value)

private abbrev bitRuleSchedules (value : Bool) :=
  (bitDerivedRuleSchedules value).schedules

private theorem bitCoversChildren (value : Bool) :
    (bitRuleSchedules value).CoversChildren :=
  (bitDerivedRuleSchedules value).coversChildren

section BitLayerCertification

variable (value : Bool)
  (layerChildren : (child : (bitInstances value).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure (bitChildContracts value child))

private abbrev bitCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (bitBody value) layerChildren

private def bitStateCorresponds (_ : emptySignalMap.Values)
    (_ : (bitCertificationStructure value layerChildren).State) : Prop := True

private theorem bitImplements :
    Contracts.Cycle.ImplementsSolutions
      (bitCertificationStructure value layerChildren) (cycleContract .bit value)
      (bitStateCorresponds value layerChildren) := by
  intro contractState hierStep corresponds satisfies
  letI : Subsingleton
      ((bitChildContracts value .source).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have sourceMatch :=
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      (body := bitBody value) layerChildren hierStep satisfies .source
        SignalMap.emptyValues)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    have boundary := satisfies.1
    have sourceOutput : (hierStep.children .source).outputs .output = value :=
      (Primitives.constantOutputRule_holds_iff value _ _ _).mp
        (sourceMatch.ruleHolds Primitives.ConstantRule.apply)
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

private def aggregateScheduleOrders (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    ScheduleDerivation.RuleScheduleOrders (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (cycleContract splitter.aggregateType value) where
  output := fun
    | .apply => splitter.ports.outputs.labels.values.map
        (componentOccurrence splitter value) ++
      [combineOccurrence splitter value]
  state := []

private noncomputable def aggregateDerivedRuleSchedules
    (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    ScheduleDerivation.DerivedRuleSchedules (aggregateBody splitter)
      (aggregateChildContracts splitter value)
      (cycleContract splitter.aggregateType value) := by
  cases splitter with
  | vector length element =>
      derive_rule_schedules
        (aggregateScheduleOrders (.vector length element) value)
  | tuple fields =>
      derive_rule_schedules (aggregateScheduleOrders (.tuple fields) value)

private noncomputable abbrev aggregateRuleSchedules
    (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :=
  (aggregateDerivedRuleSchedules splitter value).schedules

private theorem aggregateCoversChildren (splitter : Composition.SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    (aggregateRuleSchedules splitter value).CoversChildren :=
  (aggregateDerivedRuleSchedules splitter value).coversChildren

section AggregateLayerCertification

variable (splitter : Composition.SignalSplitter)
  (value : splitter.aggregateType.Denote)
  (layerChildren : (child : (aggregateBody splitter).instancePorts.Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (aggregateChildContracts splitter value child))

private abbrev aggregateCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (aggregateBody splitter) layerChildren

private def aggregateStateCorresponds (_ : emptySignalMap.Values)
    (_ : (aggregateCertificationStructure splitter value layerChildren).State) : Prop := True

private theorem aggregateImplements :
    Contracts.Cycle.ImplementsSolutions
      (aggregateCertificationStructure splitter value layerChildren)
      (cycleContract splitter.aggregateType value)
      (aggregateStateCorresponds splitter value layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childStateSubsingleton
      (child : (aggregateBody splitter).instancePorts.Name) :
      Subsingleton
        ((aggregateChildContracts splitter value child).state.Values) := by
    cases child with
    | splitter impossible => exact nomatch impossible
    | component component => change Subsingleton emptySignalMap.Values; infer_instance
    | combiner outputName => cases outputName; change Subsingleton emptySignalMap.Values; infer_instance
  have childMatch (child : (aggregateBody splitter).instancePorts.Name) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      (body := aggregateBody splitter) layerChildren hierStep satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have boundary := satisfies.1
  have componentOutputs : ∀ component,
      (hierStep.children (.component component)).outputs .output =
        componentValue splitter value component := by
    intro component
    have holds := (childMatch (.component component)).ruleHolds Primitives.ConstantRule.apply
    change (outputRule _ (componentValue splitter value component)).Holds _ _ _ at holds
    exact (outputRule_holds_iff _ _ _ _ _).mp holds
  have combineOutputs : (hierStep.children (.combiner .output)).outputs =
      splitter.combiner.outputValues
        ((aggregateBody splitter).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (.combiner .output)) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff splitter.combiner _ _ _).mp
      ((childMatch (.combiner .output)).ruleHolds Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .output = value
    cases splitter with
    | vector length element =>
        have boundaryOutput := boundary .output
        change hierStep.outputs .output =
          (hierStep.children (.combiner .output)).outputs
            Composition.AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs Composition.AggregatePort.value]
        change (fun component =>
          (hierStep.children (.component component)).outputs .output) = value
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryOutput := boundary .output
        change hierStep.outputs .output =
          (hierStep.children (.combiner .output)).outputs
            Composition.AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs Composition.AggregatePort.value]
        change fields.assemble (fun component =>
          (hierStep.children (.component component)).outputs .output) = value
        calc
          fields.assemble (fun component =>
              (hierStep.children (.component component)).outputs .output) =
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
    (child : (aggregateBody splitter).instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (aggregateChildContracts splitter value child)
  | .splitter impossible => nomatch impossible
  | .component component =>
      ⟨moduleStructure (splitter.ports.outputs.signalType component)
        (componentValue splitter value component), components component⟩
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
  | .vector length elementType, value =>
      aggregateImplementation (.vector length elementType) value fun component =>
        implementationDefinition elementType (value component)
  | .tuple fields, value =>
      aggregateImplementation (.tuple fields) value fun component =>
        implementationDefinition (fields.typeAt component) (fields.get value component)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

private noncomputable opaque implementation (signalType : SignalType)
    (value : signalType.Denote) :
    Implementation signalType value := implementationDefinition signalType value

noncomputable def certification (signalType : SignalType) (value : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType value)
      (cycleContract signalType value) :=
  implementation signalType value

noncomputable def certified (signalType : SignalType) (value : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType value).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).moduleStructure = moduleStructure signalType value :=
  rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).cycleContract = cycleContract signalType value :=
  rfl

module_cycle_realization_bridge allowed_of_realization
  (signalType : SignalType) (value : signalType.Denote)
  for moduleStructure signalType value
  implementing cycleContract signalType value using certification

/-- Contract-facing constant result law. -/
theorem output_of_allowed (signalType : SignalType) (value : signalType.Denote)
    {step : (cycleContract signalType value).Step}
    (allowed : (cycleContract signalType value).Allows step) :
    step.outputs .output = value :=
  (outputRule_holds_iff signalType value _ _ _).mp (allowed.1 .apply)

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
  | .vector length elementType, value, typeNaming => by
      rw [Modules.Constant.moduleStructure.eq_def]
      let splitter : Composition.SignalSplitter := .vector length elementType
      exact .composite
        ⟨"constant", "structural",
          .signalType splitter.aggregateType :: valueParameters splitter.aggregateType value⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter impossible => nomatch impossible
          | .component component => .scoped "constant" (.indexed "component" component.val)
          | .combiner .output => "combine")
        (fun
          | .splitter impossible => nomatch impossible
          | .component component =>
              namingWith elementType (value component) (typeNaming.component component)
          | .combiner .output =>
              Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner
                typeNaming)
  | .tuple fields, value, typeNaming => by
      rw [Modules.Constant.moduleStructure.eq_def]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite
        ⟨"constant", "structural",
          .signalType splitter.aggregateType :: valueParameters splitter.aggregateType value⟩
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
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

def naming (signalType : SignalType) (value : signalType.Denote) :
    ModuleNaming (Modules.Constant.moduleStructure signalType value) :=
  namingWith signalType value (.positional signalType)

end Silean.Modules.Constant.Naming

namespace Silean.Modules.Constant

@[reducible] def designWith (signalType : SignalType) (value : signalType.Denote)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
  Silean.Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType value
  naming := (Naming.namingWith signalType value typeNaming).withPorts
    (Naming.portsWithNaming signalType typeNaming)

@[reducible] def design (signalType : SignalType) (value : signalType.Denote) :
    Silean.Naming.NamedModule :=
  designWith signalType value (.positional signalType)

/-! ## Placement -/

open Silean.Authoring.CircuitDescription

/-- Place a constant source under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (signalType : SignalType) (value : signalType.Denote) :
    Builder (Net signalType) := do
  let child <- Authoring.CircuitDescription.placeNamed name
    (design signalType value) fun impossible => nomatch impossible
  pure (child .output)

/-- Place a constant source using the next conventional indexed name. -/
noncomputable def place (signalType : SignalType) (value : signalType.Denote) :
    Builder (Net signalType) := do
  let child <- placeIndexed "constant" (design signalType value)
    fun impossible => nomatch impossible
  pure (child .output)

attribute [circuit_description] placeNamed place

end Silean.Modules.Constant
