import Silean.CertifiedSchedule
import Silean.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Constant

open Silean

abbrev Output := Primitives.SingleOutput

@[reducible] private def interface : LeafwiseInterface where
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
    CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (ports signalType).outputs.select .output
  target | (), _ => (value, ())

@[reducible] def cycleContract (signalType : SignalType)
    (value : signalType.Denote) : ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType value⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (value : signalType.Denote) (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values) (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType value).Holds inputs state outputs ↔
      outputs .output = value := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

private inductive BitInstance | source
deriving Enumeration

@[reducible] private def bitInstances (value : Bool) : Instances :=
  EnumeratedMap.of BitInstance fun | .source => (Primitives.constant value).ports

@[reducible] private def bitContext (value : Bool) : EndpointContext where
  ports := ports .bit
  instances := bitInstances value

private def bitWiring (value : Bool) :
    Wiring (bitContext value).ports (bitContext value).instances where
  moduleOutput | .output => (bitContext value).instanceOutput .source .output
  instanceInput | .source, impossible => nomatch impossible

@[reducible] private def bitBody (value : Bool) : ModuleBody :=
  ⟨bitContext value, bitWiring value⟩

@[reducible] private def bitChildren (value : Bool) :
    Certified.Children (bitBody value)
  | .source => Primitives.constantCertified value

private def bitModuleStructure (value : Bool) : ModuleStructure (ports .bit) :=
  Certified.moduleStructure (bitBody value) (bitChildren value)

def moduleStructure : (signalType : SignalType) → signalType.Denote →
    ModuleStructure (ports signalType)
  | .bit, value => bitModuleStructure value
  | .vector length element, value =>
      let splitter : SignalSplitter := .vector length element
      .composite (interface.aggregateBody splitter) fun
        | .splitter impossible => nomatch impossible
        | .component component => moduleStructure element (value component)
        | .combiner _ => .combiner splitter.combiner
  | .tuple fields, value =>
      let splitter : SignalSplitter := .tuple fields
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

private abbrev Implementation (signalType : SignalType) (value : signalType.Denote) :=
  ModuleCycleCertification (moduleStructure signalType value)
    (cycleContract signalType value)

private def Implementation.certified
    (implementation : Implementation signalType value) :
    ModuleCycleCertified (ports signalType) := implementation.bundle

private abbrev bitOccurrence (value : Bool) :
    Certified.RuleOccurrence (bitChildren value) :=
  ⟨.source, Primitives.ConstantRule.apply⟩

private def bitOutputSchedule (value : Bool) :
    Certified.OutputSchedule (bitBody value) (bitChildren value)
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
    Certified.StateSchedule (bitBody value) (bitChildren value) :=
  .done (by
    intro child input member
    cases child
    simp [bitChildren, Primitives.constantCertified,
      Primitives.constantCycleContract, CycleStateRule.empty,
      SignalSelection.labels] at member)

private def bitRuleSchedules (value : Bool) :
    Certified.RuleSchedules (bitBody value) (bitChildren value)
      (cycleContract .bit value) where
  output | .apply => bitOutputSchedule value
  state := bitStateSchedule value

private theorem bitCoversChildren (value : Bool) :
    (bitRuleSchedules value).CoversChildren := by
  intro child rule
  cases child
  change Primitives.ConstantRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs (bitRuleSchedules value) .apply
  change bitOccurrence value ∈ (bitOutputSchedule value).finalAvailability
  simp [bitOutputSchedule, Certified.Schedule.finalAvailability]

private theorem bitHasStructuralResult (value : Bool)
    (inputs : (ports .bit).inputs.Values) (state : (bitModuleStructure value).State) :
    ∃ proposal, (bitModuleStructure value).IsSolution inputs state proposal := by
  have available := (Primitives.constantCertified value).hasStructuralResult
    (fun impossible => nomatch impossible) (state .source)
  rcases available with ⟨source, sourceSatisfies⟩
  let children : (name : BitInstance) →
      ProposedValues (Certified.childStructure (bitChildren value) name)
    | .source => source
  let outputs : (ports .bit).outputs.Values := fun
    | .output => source.outputs .output
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro outputName
    cases outputName
    rfl
  · intro child
    cases child
    change (Primitives.constantCertified value).moduleStructure.IsSolution
      (ProposedValues.childInputs (bitBody value)
        (Certified.childStructure (bitChildren value)) inputs children .source)
      (state .source) source
    have childInputs_eq : ProposedValues.childInputs (bitBody value)
        (Certified.childStructure (bitChildren value)) inputs children .source =
        (fun impossible => nomatch impossible) := by
      funext impossible
      exact nomatch impossible
    rw [childInputs_eq]
    exact sourceSatisfies

private theorem bitImplements (value : Bool) :
    Implements (bitModuleStructure value) (cycleContract .bit value)
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have sourceSatisfies := childSatisfies .source
  have sourceOutput : (children .source).outputs .output = value := by
    exact congrFun sourceSatisfies.1 .output
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    exact (boundary .output).trans sourceOutput
  · rfl

private def bitCertification (value : SignalType.bit.Denote) :
    ModuleCycleCertification (bitModuleStructure value)
      (cycleContract .bit value) := {
    stateCorresponds := fun _ _ => True
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := bitHasStructuralResult value
    structuralResultUnique := (bitRuleSchedules value).hasAtMostOneSolution
      (bitCoversChildren value)
    implements := bitImplements value }

private def bitImplementation (value : SignalType.bit.Denote) :
    Implementation .bit value :=
  (bitCertification value).transportStructure (moduleStructure_bit value).symm

@[reducible] private def aggregateBody (splitter : SignalSplitter) :=
  interface.aggregateBody splitter

@[reducible] private def componentValue (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (component : splitter.ports.outputs.Label) :
    (splitter.ports.outputs.signalType component).Denote :=
  splitter.outputValues (splitter.inputValues value) component

@[reducible] private def aggregateChildren (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.Children (aggregateBody splitter) :=
  interface.aggregateChildren splitter fun component =>
    (components component).certified

@[reducible] private def aggregateChildStructure (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :=
  Certified.childStructure (aggregateChildren splitter value components)

private theorem aggregateModuleStructure_eq (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    moduleStructure splitter.aggregateType value =
      Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter value components) := by
  cases splitter with
  | vector length element =>
      simp only [SignalSplitter.aggregateType, moduleStructure,
        Certified.moduleStructure]
      congr
      funext child
      cases child with
      | splitter impossible => exact nomatch impossible
      | component component => rfl
      | combiner outputName => cases outputName; rfl
  | tuple fields =>
      simp only [SignalSplitter.aggregateType, moduleStructure,
        Certified.moduleStructure]
      congr
      funext child
      cases child with
      | splitter impossible => exact nomatch impossible
      | component component => rfl
      | combiner outputName => cases outputName; rfl

private def combinerInputs (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component))
    (proposals : (component : splitter.ports.outputs.Label) →
      ProposedValues
        (moduleStructure (splitter.ports.outputs.signalType component)
          (componentValue splitter value component))) :
    splitter.combiner.ports.inputs.Values := by
  cases splitter <;> exact fun component => (proposals component).outputs .output

private def aggregateOutputs (splitter : SignalSplitter)
    (combineProposal : ProposedValues splitter.combiner.certified.moduleStructure) :
    (ports splitter.aggregateType).outputs.Values :=
  match splitter with
  | .vector _ _ => fun | .output => combineProposal.outputs .value
  | .tuple _ => fun | .output => combineProposal.outputs .value

private def aggregateProposalConstruction (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    interface.AggregateProposalConstruction splitter
      (fun component => (components component).certified) where
  splitterInputs _ impossible := nomatch impossible
  componentInputs _ _ _ impossible := nomatch impossible
  combinerInputs componentProposals _ :=
    combinerInputs splitter value components componentProposals
  outputs combineProposals := aggregateOutputs splitter (combineProposals .output)
  boundary_eq := by
    intro inputs splitProposals componentProposals combineProposals outputName
    cases outputName
    cases splitter <;> rfl
  splitterInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals impossible
    exact nomatch impossible
  componentInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals component
    funext impossible
    exact nomatch impossible
  combinerInputs_eq := by
    intro inputs splitProposals componentProposals combineProposals outputName
    cases outputName
    cases splitter <;> funext component <;> rfl

private theorem aggregateHasStructuralResult (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component))
    (inputs : (ports splitter.aggregateType).inputs.Values)
    (state : (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter value components)).State) :
    ∃ proposal,
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter value components)).IsSolution
          inputs state proposal :=
  (aggregateProposalConstruction splitter value components).hasStructuralResult
    inputs state

private abbrev componentOccurrence (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component))
    (component : splitter.ports.outputs.Label) :
    Certified.RuleOccurrence (aggregateChildren splitter value components) :=
  interface.componentOccurrence splitter
    (fun component => (components component).certified) component .apply

private abbrev combineOccurrence (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.RuleOccurrence (aggregateChildren splitter value components) :=
  interface.combinerOccurrence splitter
    (fun component => (components component).certified) .output

private noncomputable def componentSchedule (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.Schedule (aggregateBody splitter)
      (aggregateChildren splitter value components)
      (fun input => input ∈
        (outputRule splitter.aggregateType value).readsInputs.labels)
      (fun final =>
        (∀ called, called ∈ [] → called ∈ final) ∧
        (∀ component, componentOccurrence splitter value components component ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [] ∨
            ∃ component, called = componentOccurrence splitter value components component)
      [] :=
  interface.callComponentsAfter splitter
    (fun component => (components component).certified) []
    (fun _ => Primitives.ConstantRule.apply)
    (by simp)
    (by intro component input member; exact nomatch input)

private theorem aggregateBoundaryReady (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component))
    {available : Certified.Availability
      (aggregateChildren splitter value components)}
    (combineAvailable : combineOccurrence splitter value components ∈ available) :
    Certified.BoundaryReady (aggregateBody splitter)
      (aggregateChildren splitter value components)
      ((outputRule splitter.aggregateType value).writesOutputs.labels)
      (fun input => input ∈
        (outputRule splitter.aggregateType value).readsInputs.labels)
      available := by
  intro outputName member
  cases outputName
  cases splitter <;>
    exact ⟨SignalComponentRule.apply, combineAvailable,
      by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩

private noncomputable def aggregateOutputSchedule (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.OutputSchedule (aggregateBody splitter)
      (aggregateChildren splitter value components)
      (cycleContract splitter.aggregateType value) .apply := by
  apply (componentSchedule splitter value components).append
  refine .call (combineOccurrence splitter value components) ?_ ?_ (.done ?_)
  · intro input member
    cases splitter <;>
      exact ⟨Primitives.ConstantRule.apply,
        (componentSchedule _ value components).finished.2.1 input,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩
  · intro present
    rcases (componentSchedule splitter value components).finished.2.2 _ present with
      atStart | ⟨component, equal⟩
    · simp at atStart
    · cases equal
  · exact aggregateBoundaryReady splitter value components (by simp)

private def aggregateStateSchedule (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.StateSchedule (aggregateBody splitter)
      (aggregateChildren splitter value components) :=
  .done (by
    intro child input member
    cases child with
    | splitter impossible => exact nomatch impossible
    | component component =>
        simp [aggregateChildren, LeafwiseInterface.aggregateChildren,
          Implementation.certified, ModuleCycleCertification.bundle,
          cycleContract, CycleStateRule.empty, SignalSelection.labels] at member
    | combiner outputName =>
        cases outputName
        simp [aggregateChildren, LeafwiseInterface.aggregateChildren,
          SignalCombiner.certified, SignalCombiner.cycleContract,
          CycleStateRule.empty, SignalSelection.labels] at member)

private noncomputable def aggregateRuleSchedules (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Certified.RuleSchedules (aggregateBody splitter)
      (aggregateChildren splitter value components)
      (cycleContract splitter.aggregateType value) where
  output | .apply => aggregateOutputSchedule splitter value components
  state := aggregateStateSchedule splitter value components

private theorem component_mem_outputSchedule (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component))
    (component : splitter.ports.outputs.Label) :
    componentOccurrence splitter value components component ∈
      (aggregateOutputSchedule splitter value components).finalAvailability := by
  unfold aggregateOutputSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_of_mem _
    ((componentSchedule splitter value components).finished.2.1 component)

private theorem combine_mem_outputSchedule (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    combineOccurrence splitter value components ∈
      (aggregateOutputSchedule splitter value components).finalAvailability := by
  unfold aggregateOutputSchedule
  rw [Certified.Schedule.finalAvailability_append]
  exact List.mem_cons_self

private theorem aggregateCoversChildren (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    (aggregateRuleSchedules splitter value components).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (aggregateRuleSchedules splitter value components) .apply
  cases child with
  | splitter impossible => exact nomatch impossible
  | component component =>
      change Rule at rule
      cases rule
      exact component_mem_outputSchedule splitter value components component
  | combiner outputName =>
      cases outputName
      change SignalComponentRule at rule
      cases rule
      exact combine_mem_outputSchedule splitter value components

private theorem aggregateHasAtMostOneSolution (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    (Certified.moduleStructure (aggregateBody splitter)
      (aggregateChildren splitter value components)).HasAtMostOneSolution :=
  (aggregateRuleSchedules splitter value components).hasAtMostOneSolution
    (aggregateCoversChildren splitter value components)

private theorem aggregateImplements (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Implements
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter value components))
      (cycleContract splitter.aggregateType value) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have componentOutputs : ∀ component,
      (childProposals (.component component)).outputs .output =
        componentValue splitter value component := by
    intro component
    rcases (components component).hasCorrespondingState
        (structuralState (.component component)) with
      ⟨componentState, componentCorresponds⟩
    rcases (components component).implements
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter value components) inputs childProposals
          (.component component))
        componentState (structuralState (.component component))
        (childProposals (.component component)) componentCorresponds
        (childSatisfies (.component component)) with
      ⟨nextState, evaluates, nextCorresponds⟩
    have holds := evaluates.1 Primitives.ConstantRule.apply
    exact (outputRule_holds_iff _ _ _ _ _).mp holds
  have combineOutputs : (childProposals (.combiner .output)).outputs =
      splitter.combiner.outputValues
        (ProposedValues.childInputs (aggregateBody splitter)
          (aggregateChildStructure splitter value components) inputs childProposals
          (.combiner .output)) := by
    cases splitter <;> exact childSatisfies (.combiner .output)
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
          (childProposals (.combiner .output)).outputs AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs AggregatePort.value]
        change (fun component =>
          (childProposals (.component component)).outputs .output) = value
        funext component
        exact componentOutputs component
    | tuple fields =>
        have boundaryOutput := boundary .output
        change outputs .output =
          (childProposals (.combiner .output)).outputs AggregatePort.value at boundaryOutput
        rw [boundaryOutput, congrFun combineOutputs AggregatePort.value]
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

private noncomputable def aggregateCertification (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    ModuleCycleCertification
      (Certified.moduleStructure (aggregateBody splitter)
        (aggregateChildren splitter value components))
      (cycleContract splitter.aggregateType value) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := aggregateHasStructuralResult splitter value components
  structuralResultUnique := aggregateHasAtMostOneSolution splitter value components
  implements := aggregateImplements splitter value components

private noncomputable def aggregateImplementation (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote)
    (components : (component : splitter.ports.outputs.Label) →
      Implementation (splitter.ports.outputs.signalType component)
        (componentValue splitter value component)) :
    Implementation splitter.aggregateType value :=
  (aggregateCertification splitter value components).transportStructure
    (aggregateModuleStructure_eq splitter value components).symm

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
    (value : signalType.Denote) : ModuleCycleCertified (ports signalType) :=
  (implementation signalType value).certified

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).moduleStructure = moduleStructure signalType value :=
  rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (value : signalType.Denote) :
    (certified signalType value).cycleContract = cycleContract signalType value :=
  rfl

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
      let splitter : SignalSplitter := .vector length element
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
      let splitter : SignalSplitter := .tuple fields
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
