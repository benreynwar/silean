import Silean.Contracts.Cycle.CycleLayerSchedule
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Composition

/-! Generic hierarchy for modules whose aggregate behavior is obtained by
applying the same module independently to every immediate signal component.

Public input labels remain chosen by the module.  `inputLayout` only classifies
them internally as recursively split inputs or fixed-shape inputs which are
broadcast unchanged to every component.  Outputs and state are recursive: each
has the current signal type. -/

structure LabelPartition (Whole Left Right : Type) where
  classify : Whole → Sum Left Right
  label : Sum Left Right → Whole
  classify_label : ∀ part, classify (label part) = part
  label_classify : ∀ whole, label (classify whole) = whole

structure LeafwiseInterface where
  Input : Type
  inputs : Enumeration Input
  RecursiveInput : Type
  recursiveInputs : Enumeration RecursiveInput
  FixedInput : Type
  fixedInputs : Enumeration FixedInput
  inputLayout : LabelPartition Input RecursiveInput FixedInput
  fixedInputType : FixedInput → SignalType
  Output : Type
  outputs : Enumeration Output
  State : Type
  states : Enumeration State

namespace LeafwiseInterface

@[reducible] def inputType (interface : LeafwiseInterface)
    (signalType : SignalType) (input : interface.Input) : SignalType :=
  match interface.inputLayout.classify input with
  | .inl _ => signalType
  | .inr fixed => interface.fixedInputType fixed

@[reducible] def inputMap (interface : LeafwiseInterface)
    (signalType : SignalType) : SignalMap where
  Key := interface.Input
  keys := interface.inputs
  value := interface.inputType signalType

@[reducible] def outputMap (interface : LeafwiseInterface)
    (signalType : SignalType) : SignalMap where
  Key := interface.Output
  keys := interface.outputs
  value := fun _ => signalType

@[reducible] def stateMap (interface : LeafwiseInterface)
    (signalType : SignalType) : SignalMap where
  Key := interface.State
  keys := interface.states
  value := fun _ => signalType

@[reducible] def ports (interface : LeafwiseInterface)
    (signalType : SignalType) : ModulePorts :=
  ⟨interface.inputMap signalType, interface.outputMap signalType⟩

inductive AggregateInstance (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
  /-- Splits one recursively shaped input into immediate components. -/
  | splitter (input : interface.RecursiveInput)
  /-- Applies the component module recursively at one position. -/
  | component (component : splitter.ports.outputs.Label)
  /-- Reassembles one recursively shaped output. -/
  | combiner (output : interface.Output)

@[reducible] def aggregateInstanceEnumeration (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) :
    Enumeration (AggregateInstance interface splitter) where
  values :=
    interface.recursiveInputs.values.map AggregateInstance.splitter ++ (
      splitter.ports.outputs.labels.values.map AggregateInstance.component ++
      interface.outputs.values.map AggregateInstance.combiner)
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_map_of_injective AggregateInstance.splitter ?_
      interface.recursiveInputs.nodup, ?_, ?_⟩
    · intro left right equal; cases equal; rfl
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_map_of_injective AggregateInstance.component ?_
        splitter.ports.outputs.labels.nodup,
        List.nodup_map_of_injective AggregateInstance.combiner ?_
          interface.outputs.nodup, ?_⟩
      · intro left right equal; cases equal; rfl
      · intro left right equal; cases equal; rfl
      · intro left leftMem right rightMem equal
        rcases List.mem_map.mp leftMem with ⟨left, _, rfl⟩
        rcases List.mem_map.mp rightMem with ⟨right, _, rfl⟩
        cases equal
    · intro left leftMem right rightMem equal
      rcases List.mem_map.mp leftMem with ⟨left, _, rfl⟩
      rcases List.mem_append.mp rightMem with rightMem | rightMem
      · rcases List.mem_map.mp rightMem with ⟨right, _, rfl⟩
        cases equal
      · rcases List.mem_map.mp rightMem with ⟨right, _, rfl⟩
        cases equal
  locate
    | .splitter input =>
        (interface.recursiveInputs.locate input).map AggregateInstance.splitter
          |>.appendRight
            (splitter.ports.outputs.labels.values.map
              AggregateInstance.component ++
              interface.outputs.values.map AggregateInstance.combiner)
    | .component component =>
        (splitter.ports.outputs.labels.locate component).map
          AggregateInstance.component
          |>.appendRight
            (interface.outputs.values.map AggregateInstance.combiner)
          |>.prependMany
            (interface.recursiveInputs.values.map AggregateInstance.splitter)
    | .combiner output =>
        (interface.outputs.locate output).map AggregateInstance.combiner
          |>.prependMany
            (splitter.ports.outputs.labels.values.map
              AggregateInstance.component)
          |>.prependMany
            (interface.recursiveInputs.values.map AggregateInstance.splitter)

@[reducible] def aggregateInstances (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) : InstancePorts where
  Key := AggregateInstance interface splitter
  keys := interface.aggregateInstanceEnumeration splitter
  value
    | .splitter _ => splitter.ports
    | .component component =>
        interface.ports (splitter.ports.outputs.signalType component)
    | .combiner _ => splitter.combiner.ports

@[reducible] def aggregateContext (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) : EndpointContext where
  ports := interface.ports splitter.aggregateType
  instancePorts := interface.aggregateInstances splitter

private theorem recursiveInputType (interface : LeafwiseInterface)
    (signalType : SignalType) (input : interface.RecursiveInput) :
    interface.inputType signalType
      (interface.inputLayout.label (.inl input)) = signalType := by
  simp [inputType, interface.inputLayout.classify_label]

def aggregateModuleOutputSource (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) (output : interface.Output) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instancePorts splitter.aggregateType :=
  match splitter with
  | .vector length element =>
      (interface.aggregateContext (.vector length element)).instanceOutput
        (.combiner output) Composition.AggregatePort.value
  | .tuple fields =>
      (interface.aggregateContext (.tuple fields)).instanceOutput
        (.combiner output) Composition.AggregatePort.value

def aggregateSplitterInputSource (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) (recursiveInput : interface.RecursiveInput) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instancePorts splitter.aggregateType :=
  match splitter with
  | .vector length element => by
      change SignalSource _ _ (.vector length element)
      rw [← interface.recursiveInputType (.vector length element) recursiveInput]
      exact (interface.aggregateContext (.vector length element)).moduleInput
        (interface.inputLayout.label (.inl recursiveInput))
  | .tuple fields => by
      change SignalSource _ _ (.tuple fields)
      rw [← interface.recursiveInputType (.tuple fields) recursiveInput]
      exact (interface.aggregateContext (.tuple fields)).moduleInput
        (interface.inputLayout.label (.inl recursiveInput))

def aggregateComponentInputSource (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) (component : splitter.ports.outputs.Label)
    (input : (interface.ports
      (splitter.ports.outputs.signalType component)).inputs.Label) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instancePorts
      ((interface.ports
        (splitter.ports.outputs.signalType component)).inputs.signalType input) :=
  match splitter with
  | .vector length element =>
      match layout : interface.inputLayout.classify input with
      | .inl recursiveInput => by
          change SignalSource _ _ (interface.inputType element input)
          rw [inputType, layout]
          exact (interface.aggregateContext
            (.vector length element)).instanceOutput
              (.splitter recursiveInput) component
      | .inr fixedInput => by
          rw [← interface.inputLayout.label_classify input, layout]
          change SignalSource _ _
            (interface.inputType element
              (interface.inputLayout.label (.inr fixedInput)))
          have source := (interface.aggregateContext
            (.vector length element)).moduleInput
              (interface.inputLayout.label (.inr fixedInput))
          change SignalSource _ _
            (interface.inputType (.vector length element)
              (interface.inputLayout.label (.inr fixedInput))) at source
          simpa only [inputType,
            interface.inputLayout.classify_label] using source
  | .tuple fields =>
      match layout : interface.inputLayout.classify input with
      | .inl recursiveInput => by
          change SignalSource _ _
            (interface.inputType (fields.typeAt component) input)
          rw [inputType, layout]
          exact (interface.aggregateContext (.tuple fields)).instanceOutput
            (.splitter recursiveInput) component
      | .inr fixedInput => by
          rw [← interface.inputLayout.label_classify input, layout]
          change SignalSource _ _
            (interface.inputType (fields.typeAt component)
              (interface.inputLayout.label (.inr fixedInput)))
          have source :=
            (interface.aggregateContext (.tuple fields)).moduleInput
              (interface.inputLayout.label (.inr fixedInput))
          change SignalSource _ _
            (interface.inputType (.tuple fields)
              (interface.inputLayout.label (.inr fixedInput))) at source
          simpa only [inputType,
            interface.inputLayout.classify_label] using source

def aggregateCombinerInputSource (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) (output : interface.Output)
    (component : splitter.combiner.ports.inputs.Label) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instancePorts
      (splitter.combiner.ports.inputs.signalType component) :=
  match splitter with
  | .vector length element =>
      (interface.aggregateContext (.vector length element)).instanceOutput
        (.component component) output
  | .tuple fields =>
      (interface.aggregateContext (.tuple fields)).instanceOutput
        (.component component) output

def aggregateWiring (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) :
    Wiring (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instancePorts :=
  match splitter with
  | .vector length element => {
      -- Reassembled component outputs drive the aggregate outputs.
      moduleOutput := interface.aggregateModuleOutputSource
        (.vector length element)
      instanceInput := fun
        -- Split recursive inputs, broadcast fixed inputs, then recombine outputs.
        | .splitter recursiveInput, Composition.AggregatePort.value =>
            interface.aggregateSplitterInputSource
              (.vector length element) recursiveInput
        | .component component, input =>
            interface.aggregateComponentInputSource
              (.vector length element) component input
        | .combiner output, component =>
            interface.aggregateCombinerInputSource
              (.vector length element) output component }
  | .tuple fields => {
      -- Tuple composition follows the same split/apply/combine dataflow.
      moduleOutput := interface.aggregateModuleOutputSource (.tuple fields)
      instanceInput := fun
        | .splitter recursiveInput, Composition.AggregatePort.value =>
            interface.aggregateSplitterInputSource
              (.tuple fields) recursiveInput
        | .component component, input =>
            interface.aggregateComponentInputSource
              (.tuple fields) component input
        | .combiner output, component =>
            interface.aggregateCombinerInputSource
              (.tuple fields) output component }

@[reducible] def aggregateBody (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter) : ModuleBody where
  context := interface.aggregateContext splitter
  wiring := interface.aggregateWiring splitter

/-! ## Contract boundary for an aggregate layer

The scheduling interface names only the contracts required from recursive
components. Concrete component structures and certifications are supplied
later when the layer is instantiated. -/

@[reducible] def aggregateChildContracts (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component))) :
    Contracts.Cycle.ChildCycleContracts (interface.aggregateBody splitter)
  | .splitter _ => splitter.cycleContract
  | .component component => componentContracts component
  | .combiner _ => splitter.combiner.cycleContract

abbrev splitterOccurrence (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component)))
    (recursiveInput : interface.RecursiveInput) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (interface.aggregateBody splitter)
      (interface.aggregateChildContracts splitter componentContracts) :=
  ⟨.splitter recursiveInput, Composition.SignalComponentRule.apply⟩

abbrev componentOccurrence (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component)))
    (component : splitter.ports.outputs.Label)
    (rule : (componentContracts component).RuleName) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (interface.aggregateBody splitter)
      (interface.aggregateChildContracts splitter componentContracts) :=
  ⟨.component component, rule⟩

abbrev combinerOccurrence (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component)))
    (output : interface.Output) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (interface.aggregateBody splitter)
      (interface.aggregateChildContracts splitter componentContracts) :=
  ⟨.combiner output, Composition.SignalComponentRule.apply⟩

theorem componentOccurrence_injective (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component)))
    (rule : (component : splitter.ports.outputs.Label) →
      (componentContracts component).RuleName) :
    Function.Injective (fun component =>
      interface.componentOccurrence splitter componentContracts component
        (rule component)) := by
  intro left right equal
  have childEqual : AggregateInstance.component left =
      AggregateInstance.component right :=
    congrArg Contracts.Cycle.Certification.Layer.RuleOccurrence.child equal
  exact AggregateInstance.component.inj childEqual

noncomputable def callComponentsAfter (interface : LeafwiseInterface)
    (splitter : Composition.SignalSplitter)
    (componentContracts : (component : splitter.ports.outputs.Label) →
      Contracts.Cycle.ModuleCycleContract
        (interface.ports (splitter.ports.outputs.signalType component)))
    {inputAvailable :
      (interface.aggregateBody splitter).context.ports.inputs.Label → Prop}
    (initial : Contracts.Cycle.Certification.Layer.Availability
      (interface.aggregateBody splitter)
      (interface.aggregateChildContracts splitter componentContracts))
    (rule : (component : splitter.ports.outputs.Label) →
      (componentContracts component).RuleName)
    (fresh : ∀ component,
      interface.componentOccurrence splitter componentContracts component
        (rule component) ∉ initial)
    (readsAvailable : ∀ component input,
      input ∈ (interface.componentOccurrence splitter componentContracts component
        (rule component)).reads →
      Contracts.Cycle.Certification.Layer.sourceAvailable inputAvailable initial
        ((interface.aggregateBody splitter).wiring.instanceInput
          (.component component) input)) :
    Contracts.Cycle.Certification.Layer.Schedule
      (interface.aggregateBody splitter)
      (interface.aggregateChildContracts splitter componentContracts)
      inputAvailable
      (fun final =>
        (∀ called, called ∈ initial → called ∈ final) ∧
        (∀ component,
          interface.componentOccurrence splitter componentContracts component
            (rule component) ∈ final) ∧
        ∀ called, called ∈ final → called ∈ initial ∨
          ∃ component, called =
            interface.componentOccurrence splitter componentContracts component
              (rule component)) initial :=
  Contracts.Cycle.Certification.Layer.Schedule.callFamilyAfter initial
    splitter.ports.outputs.labels
    (fun component => interface.componentOccurrence splitter componentContracts
      component (rule component))
    (interface.componentOccurrence_injective splitter componentContracts rule)
    fresh readsAvailable

@[reducible] def moduleStructure (interface : LeafwiseInterface)
    (bitStructure : ModuleStructure (interface.ports .bit)) :
    (signalType : SignalType) → ModuleStructure (interface.ports signalType)
  | .bit => bitStructure
  | .vector length element =>
      .composite (interface.aggregateBody (.vector length element)) fun
        | .splitter _ => .splitter (.vector length element)
        | .component _ => interface.moduleStructure bitStructure element
        | .combiner _ => .combiner (.vector length element)
  | .tuple fields =>
      .composite (interface.aggregateBody (.tuple fields)) fun
        | .splitter _ => .splitter (.tuple fields)
        | .component component =>
            interface.moduleStructure bitStructure (fields.typeAt component)
        | .combiner _ => .combiner (.tuple fields)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

end LeafwiseInterface

end Silean.Composition
