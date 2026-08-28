import Silean.CertifiedSchedule
import Silean.SignalAdapterCertified

namespace Silean

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
    (splitter : SignalSplitter)
  | splitter (input : interface.RecursiveInput)
  | component (component : splitter.ports.outputs.Label)
  | combiner (output : interface.Output)

@[reducible] def aggregateInstanceEnumeration (interface : LeafwiseInterface)
    (splitter : SignalSplitter) :
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
    (splitter : SignalSplitter) : Instances where
  Key := AggregateInstance interface splitter
  keys := interface.aggregateInstanceEnumeration splitter
  value
    | .splitter _ => splitter.ports
    | .component component =>
        interface.ports (splitter.ports.outputs.signalType component)
    | .combiner _ => splitter.combiner.ports

@[reducible] def aggregateContext (interface : LeafwiseInterface)
    (splitter : SignalSplitter) : EndpointContext where
  ports := interface.ports splitter.aggregateType
  instances := interface.aggregateInstances splitter

private theorem recursiveInputType (interface : LeafwiseInterface)
    (signalType : SignalType) (input : interface.RecursiveInput) :
    interface.inputType signalType
      (interface.inputLayout.label (.inl input)) = signalType := by
  simp [inputType, interface.inputLayout.classify_label]

def aggregateModuleOutputSource (interface : LeafwiseInterface)
    (splitter : SignalSplitter) (output : interface.Output) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instances splitter.aggregateType :=
  match splitter with
  | .vector length element =>
      (interface.aggregateContext (.vector length element)).instanceOutput
        (.combiner output) AggregatePort.value
  | .tuple fields =>
      (interface.aggregateContext (.tuple fields)).instanceOutput
        (.combiner output) AggregatePort.value

def aggregateSplitterInputSource (interface : LeafwiseInterface)
    (splitter : SignalSplitter) (recursiveInput : interface.RecursiveInput) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instances splitter.aggregateType :=
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
    (splitter : SignalSplitter) (component : splitter.ports.outputs.Label)
    (input : (interface.ports
      (splitter.ports.outputs.signalType component)).inputs.Label) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instances
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
    (splitter : SignalSplitter) (output : interface.Output)
    (component : splitter.combiner.ports.inputs.Label) :
    SignalSource (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instances
      (splitter.combiner.ports.inputs.signalType component) :=
  match splitter with
  | .vector length element =>
      (interface.aggregateContext (.vector length element)).instanceOutput
        (.component component) output
  | .tuple fields =>
      (interface.aggregateContext (.tuple fields)).instanceOutput
        (.component component) output

def aggregateWiring (interface : LeafwiseInterface)
    (splitter : SignalSplitter) :
    Wiring (interface.aggregateContext splitter).ports
      (interface.aggregateContext splitter).instances :=
  match splitter with
  | .vector length element => {
      moduleOutput := interface.aggregateModuleOutputSource
        (.vector length element)
      instanceInput := fun
        | .splitter recursiveInput, AggregatePort.value =>
            interface.aggregateSplitterInputSource
              (.vector length element) recursiveInput
        | .component component, input =>
            interface.aggregateComponentInputSource
              (.vector length element) component input
        | .combiner output, component =>
            interface.aggregateCombinerInputSource
              (.vector length element) output component }
  | .tuple fields => {
      moduleOutput := interface.aggregateModuleOutputSource (.tuple fields)
      instanceInput := fun
        | .splitter recursiveInput, AggregatePort.value =>
            interface.aggregateSplitterInputSource
              (.tuple fields) recursiveInput
        | .component component, input =>
            interface.aggregateComponentInputSource
              (.tuple fields) component input
        | .combiner output, component =>
            interface.aggregateCombinerInputSource
              (.tuple fields) output component }

@[reducible] def aggregateBody (interface : LeafwiseInterface)
    (splitter : SignalSplitter) : ModuleBody where
  context := interface.aggregateContext splitter
  wiring := interface.aggregateWiring splitter

/-! Certification-facing views of the same hierarchy.  Components may carry
different contracts; only their public ports and certification are needed to
construct and prove a structural proposal. -/

@[reducible] def aggregateChildren (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component))) :
    Certified.Children (interface.aggregateBody splitter)
  | .splitter _ => splitter.certified
  | .component component => components component
  | .combiner _ => splitter.combiner.certified

@[reducible] def aggregateChildStructure (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component))) :=
  Certified.childStructure (interface.aggregateChildren splitter components)

abbrev splitterOccurrence (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    (recursiveInput : interface.RecursiveInput) :
    Certified.RuleOccurrence
      (interface.aggregateChildren splitter components) :=
  ⟨.splitter recursiveInput, SignalComponentRule.apply⟩

abbrev componentOccurrence (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    (component : splitter.ports.outputs.Label)
    (rule : (components component).cycleContract.RuleName) :
    Certified.RuleOccurrence
      (interface.aggregateChildren splitter components) :=
  ⟨.component component, rule⟩

abbrev combinerOccurrence (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    (output : interface.Output) :
    Certified.RuleOccurrence
      (interface.aggregateChildren splitter components) :=
  ⟨.combiner output, SignalComponentRule.apply⟩

theorem componentOccurrence_injective (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    (rule : (component : splitter.ports.outputs.Label) →
      (components component).cycleContract.RuleName) :
    Function.Injective (fun component =>
      interface.componentOccurrence splitter components component
        (rule component)) := by
  intro left right equal
  have childEqual : AggregateInstance.component left =
      AggregateInstance.component right :=
    congrArg Certified.RuleOccurrence.child equal
  exact AggregateInstance.component.inj childEqual

noncomputable def callComponentsAfter (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    {inputAvailable : (interface.aggregateBody splitter).context.ports.inputs.Label → Prop}
    (initial : Certified.Availability
      (interface.aggregateChildren splitter components))
    (rule : (component : splitter.ports.outputs.Label) →
      (components component).cycleContract.RuleName)
    (fresh : ∀ component,
      interface.componentOccurrence splitter components component
        (rule component) ∉ initial)
    (readsAvailable : ∀ component input,
      input ∈ (interface.componentOccurrence splitter components component
        (rule component)).reads →
      Certified.sourceAvailable inputAvailable initial
        ((interface.aggregateBody splitter).wiring.instanceInput
          (.component component) input)) :
    Certified.Schedule (interface.aggregateBody splitter)
      (interface.aggregateChildren splitter components) inputAvailable
      (fun final =>
        (∀ called, called ∈ initial → called ∈ final) ∧
        (∀ component, interface.componentOccurrence splitter components component
          (rule component) ∈ final) ∧
        ∀ called, called ∈ final → called ∈ initial ∨
          ∃ component, called = interface.componentOccurrence splitter components
            component (rule component)) initial :=
  Certified.Schedule.callFamilyAfter initial splitter.ports.outputs.labels
    (fun component => interface.componentOccurrence splitter components component
      (rule component))
    (interface.componentOccurrence_injective splitter components rule)
    fresh readsAvailable

def aggregateChildProposals (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component)))
    (splitProposals : (recursiveInput : interface.RecursiveInput) →
      ProposedValues splitter.certified.moduleStructure)
    (componentProposals : (component : splitter.ports.outputs.Label) →
      ProposedValues (components component).moduleStructure)
    (combinerProposals : (output : interface.Output) →
      ProposedValues splitter.combiner.certified.moduleStructure) :
    (child : interface.AggregateInstance splitter) →
      ProposedValues (interface.aggregateChildStructure splitter components child)
  | .splitter recursiveInput => splitProposals recursiveInput
  | .component component => componentProposals component
  | .combiner output => combinerProposals output

/-! A private proof witness for constructing an aggregate proposal.  It records
only the four semantic views of readable wiring used by the construction.
Unlike a certified module, this witness is not retained after the theorem. -/

structure AggregateProposalConstruction (interface : LeafwiseInterface)
    (splitter : SignalSplitter)
    (components : (component : splitter.ports.outputs.Label) →
      ModuleCycleCertified
        (interface.ports (splitter.ports.outputs.signalType component))) where
  splitterInputs :
    (interface.ports splitter.aggregateType).inputs.Values →
      interface.RecursiveInput → splitter.ports.inputs.Values
  componentInputs :
    (interface.ports splitter.aggregateType).inputs.Values →
      ((recursiveInput : interface.RecursiveInput) →
        ProposedValues splitter.certified.moduleStructure) →
      (component : splitter.ports.outputs.Label) →
        (interface.ports
          (splitter.ports.outputs.signalType component)).inputs.Values
  combinerInputs :
    ((component : splitter.ports.outputs.Label) →
      ProposedValues (components component).moduleStructure) →
      interface.Output → splitter.combiner.ports.inputs.Values
  outputs :
    ((output : interface.Output) →
      ProposedValues splitter.combiner.certified.moduleStructure) →
      (interface.ports splitter.aggregateType).outputs.Values
  boundary_eq : ∀ inputs splitProposals componentProposals
      combinerProposals output,
    outputs combinerProposals output =
      ((interface.aggregateBody splitter).wiring.moduleOutput output).value
        inputs fun child =>
          (interface.aggregateChildProposals splitter components splitProposals
            componentProposals combinerProposals child).outputs
  splitterInputs_eq : ∀ inputs splitProposals componentProposals
      combinerProposals recursiveInput,
    ProposedValues.childInputs (interface.aggregateBody splitter)
      (interface.aggregateChildStructure splitter components) inputs
      (interface.aggregateChildProposals splitter components splitProposals
        componentProposals combinerProposals) (.splitter recursiveInput) =
        splitterInputs inputs recursiveInput
  componentInputs_eq : ∀ inputs splitProposals componentProposals
      combinerProposals component,
    ProposedValues.childInputs (interface.aggregateBody splitter)
      (interface.aggregateChildStructure splitter components) inputs
      (interface.aggregateChildProposals splitter components splitProposals
        componentProposals combinerProposals) (.component component) =
        componentInputs inputs splitProposals component
  combinerInputs_eq : ∀ inputs splitProposals componentProposals
      combinerProposals output,
    ProposedValues.childInputs (interface.aggregateBody splitter)
      (interface.aggregateChildStructure splitter components) inputs
      (interface.aggregateChildProposals splitter components splitProposals
        componentProposals combinerProposals) (.combiner output) =
        combinerInputs componentProposals output

theorem AggregateProposalConstruction.hasStructuralResult
    (construction : AggregateProposalConstruction interface splitter components)
    (inputs : (interface.ports splitter.aggregateType).inputs.Values)
    (state : (Certified.moduleStructure (interface.aggregateBody splitter)
      (interface.aggregateChildren splitter components)).State) :
    ∃ proposal,
      (Certified.moduleStructure (interface.aggregateBody splitter)
        (interface.aggregateChildren splitter components)).IsSolution
          inputs state proposal := by
  let SplitProperty := fun recursiveInput proposal =>
    splitter.certified.moduleStructure.IsSolution
      (construction.splitterInputs inputs recursiveInput)
      (state (.splitter recursiveInput)) proposal
  have splitAvailable : ∀ recursiveInput, ∃ proposal,
      SplitProperty recursiveInput proposal := fun recursiveInput =>
    splitter.certified.hasStructuralResult
      (construction.splitterInputs inputs recursiveInput)
      (state (.splitter recursiveInput))
  rcases interface.recursiveInputs.exists_pi SplitProperty splitAvailable with
    ⟨splitProposals, splitSatisfies⟩
  let ComponentProperty := fun component proposal =>
    (components component).moduleStructure.IsSolution
      (construction.componentInputs inputs splitProposals component)
      (state (.component component)) proposal
  have componentAvailable : ∀ component, ∃ proposal,
      ComponentProperty component proposal := fun component =>
    (components component).hasStructuralResult
      (construction.componentInputs inputs splitProposals component)
      (state (.component component))
  rcases splitter.ports.outputs.labels.exists_pi ComponentProperty
      componentAvailable with ⟨componentProposals, componentSatisfies⟩
  let CombinerProperty := fun output proposal =>
    splitter.combiner.certified.moduleStructure.IsSolution
      (construction.combinerInputs componentProposals output)
      (state (.combiner output)) proposal
  have combinerAvailable : ∀ output, ∃ proposal,
      CombinerProperty output proposal := fun output =>
    splitter.combiner.certified.hasStructuralResult
      (construction.combinerInputs componentProposals output)
      (state (.combiner output))
  rcases interface.outputs.exists_pi CombinerProperty combinerAvailable with
    ⟨combinerProposals, combinerSatisfies⟩
  let childProposals := interface.aggregateChildProposals splitter components
    splitProposals componentProposals combinerProposals
  refine ⟨ProposedValues.composite (construction.outputs combinerProposals)
    childProposals, ?_⟩
  constructor
  · exact construction.boundary_eq inputs splitProposals componentProposals
      combinerProposals
  · intro child
    cases child with
    | splitter recursiveInput =>
        change splitter.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (interface.aggregateBody splitter)
            (interface.aggregateChildStructure splitter components) inputs
              childProposals (.splitter recursiveInput))
          (state (.splitter recursiveInput)) (splitProposals recursiveInput)
        rw [construction.splitterInputs_eq inputs splitProposals componentProposals
          combinerProposals recursiveInput]
        exact splitSatisfies recursiveInput
    | component component =>
        change (components component).moduleStructure.IsSolution
          (ProposedValues.childInputs (interface.aggregateBody splitter)
            (interface.aggregateChildStructure splitter components) inputs
              childProposals (.component component))
          (state (.component component)) (componentProposals component)
        rw [construction.componentInputs_eq inputs splitProposals componentProposals
          combinerProposals component]
        exact componentSatisfies component
    | combiner output =>
        change splitter.combiner.certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (interface.aggregateBody splitter)
            (interface.aggregateChildStructure splitter components) inputs
              childProposals (.combiner output))
          (state (.combiner output)) (combinerProposals output)
        rw [construction.combinerInputs_eq inputs splitProposals componentProposals
          combinerProposals output]
        exact combinerSatisfies output

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

end Silean
