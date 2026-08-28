import Silean.CertifiedSchedule
import Silean.Naming.SignalAdapterNaming
import Silean.SignalAdapterCertified

namespace Silean.Modules.VectorConcat

open Silean

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Input fun
    | .left => .vector leftWidth element
    | .right => .vector rightWidth element

@[reducible] def outputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector (leftWidth + rightWidth) element

@[reducible] def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePorts := ⟨inputMap element leftWidth rightWidth,
      outputMap element leftWidth rightWidth⟩

def concat (left : Fin leftWidth → α) (right : Fin rightWidth → α) :
    Fin (leftWidth + rightWidth) → α :=
  Fin.addCases left right

@[simp] theorem concat_left (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin leftWidth) :
    concat left right (Fin.castAdd rightWidth index) = left index := by
  simp [concat]

@[simp] theorem concat_right (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin rightWidth) :
    concat left right (Fin.natAdd leftWidth index) = right index := by
  simp [concat]

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    CycleOutputRule (ports element leftWidth rightWidth) emptySignalMap
      { inputTypes := .cons (.vector leftWidth element)
          (.cons (.vector rightWidth element) .nil)
        outputTypes := .cons (.vector (leftWidth + rightWidth) element) .nil } where
  readsInputs := ((inputMap element leftWidth rightWidth).select .right).prepend .left
  writesOutputs := (outputMap element leftWidth rightWidth).select .result
  target | (left, (right, ())), _ => (concat left right, ())

@[reducible] def cycleContract (element : SignalType)
    (leftWidth rightWidth : Nat) :
    ModuleCycleContract (ports element leftWidth rightWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule element leftWidth rightWidth⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values) :
    (outputRule element leftWidth rightWidth).Holds inputs state outputs ↔
      outputs .result = concat (inputs .left) (inputs .right) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem result_left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin leftWidth) :
    outputs .result (Fin.castAdd rightWidth index) = inputs .left index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_left _ _ index

theorem result_right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin rightWidth) :
    outputs .result (Fin.natAdd leftWidth index) = inputs .right index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_right _ _ index

private def leftSplitter (element : SignalType) (leftWidth : Nat) : SignalSplitter :=
  .vector leftWidth element

private def rightSplitter (element : SignalType) (rightWidth : Nat) : SignalSplitter :=
  .vector rightWidth element

private def combiner (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalCombiner := .vector (leftWidth + rightWidth) element

inductive Instance | leftSplit | rightSplit | combine
deriving Enumeration

@[reducible] def instances (element : SignalType) (leftWidth rightWidth : Nat) :
    Instances := EnumeratedMap.of Instance fun
  | .leftSplit => (leftSplitter element leftWidth).ports
  | .rightSplit => (rightSplitter element rightWidth).ports
  | .combine => (combiner element leftWidth rightWidth).ports

@[reducible] def context (element : SignalType) (leftWidth rightWidth : Nat) :
    EndpointContext where
  ports := ports element leftWidth rightWidth
  instances := instances element leftWidth rightWidth

def wiring (element : SignalType) (leftWidth rightWidth : Nat) :
    Wiring (context element leftWidth rightWidth).ports
      (context element leftWidth rightWidth).instances where
  moduleOutput
    | .result => (context element leftWidth rightWidth).instanceOutput .combine .value
  instanceInput
    | .leftSplit, .value =>
        (context element leftWidth rightWidth).moduleInput .left
    | .rightSplit, .value =>
        (context element leftWidth rightWidth).moduleInput .right
    | .combine, index =>
        Fin.addCases
          (fun leftIndex =>
            (context element leftWidth rightWidth).instanceOutput
              .leftSplit leftIndex)
          (fun rightIndex =>
            (context element leftWidth rightWidth).instanceOutput
              .rightSplit rightIndex)
          index

@[reducible] def body (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleBody := ⟨context element leftWidth rightWidth,
      wiring element leftWidth rightWidth⟩

@[reducible] def children (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.Children (body element leftWidth rightWidth)
  | .leftSplit => (leftSplitter element leftWidth).certified
  | .rightSplit => (rightSplitter element rightWidth).certified
  | .combine => (combiner element leftWidth rightWidth).certified

def moduleStructure (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleStructure (ports element leftWidth rightWidth) :=
  Certified.moduleStructure (body element leftWidth rightWidth)
    (children element leftWidth rightWidth)

abbrev leftOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.leftSplit, SignalComponentRule.apply⟩

abbrev rightOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.rightSplit, SignalComponentRule.apply⟩

abbrev combineOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.combine, SignalComponentRule.apply⟩

def outputSchedule (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.OutputSchedule (body element leftWidth rightWidth)
      (children element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) .apply :=
  .call (leftOccurrence element leftWidth rightWidth)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, body, wiring, context,
        EndpointContext.moduleInput])
    (by simp)
    (.call (rightOccurrence element leftWidth rightWidth)
      (by
        intro input _
        cases input
        simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
          SignalSelection.labels, Certified.sourceAvailable, body, wiring, context,
          EndpointContext.moduleInput])
      (by
        intro member
        have equal := List.mem_singleton.mp member
        have childEqual := congrArg Certified.RuleOccurrence.child equal
        cases childEqual)
      (.call (combineOccurrence element leftWidth rightWidth)
        (by
          intro index _
          refine Fin.addCases ?_ ?_ index
          · intro leftIndex
            rw [show (body element leftWidth rightWidth).wiring.instanceInput
                .combine (Fin.castAdd rightWidth leftIndex) =
              (context element leftWidth rightWidth).instanceOutput
                .leftSplit leftIndex by
              simp [body, wiring]]
            change Certified.outputAvailable
              [rightOccurrence element leftWidth rightWidth,
                leftOccurrence element leftWidth rightWidth]
              .leftSplit leftIndex
            refine ⟨SignalComponentRule.apply, by simp, ?_⟩
            change leftIndex ∈
              (leftOccurrence element leftWidth rightWidth).writes
            rw [show (leftOccurrence element leftWidth rightWidth).writes =
                (leftSplitter element leftWidth).ports.outputs.labels.values by
              change (leftSplitter element leftWidth).ports.outputs.allSelection.labels = _
              rw [SignalMap.allSelection_labels]]
            exact ListIndex.get_eq
              ((leftSplitter element leftWidth).ports.outputs.labels.locate leftIndex) ▸
                List.get_mem _ _
          · intro rightIndex
            rw [show (body element leftWidth rightWidth).wiring.instanceInput
                .combine (Fin.natAdd leftWidth rightIndex) =
              (context element leftWidth rightWidth).instanceOutput
                .rightSplit rightIndex by
              simp [body, wiring]]
            change Certified.outputAvailable
              [rightOccurrence element leftWidth rightWidth,
                leftOccurrence element leftWidth rightWidth]
              .rightSplit rightIndex
            refine ⟨SignalComponentRule.apply, by simp, ?_⟩
            change rightIndex ∈
              (rightOccurrence element leftWidth rightWidth).writes
            rw [show (rightOccurrence element leftWidth rightWidth).writes =
                (rightSplitter element rightWidth).ports.outputs.labels.values by
              change (rightSplitter element rightWidth).ports.outputs.allSelection.labels = _
              rw [SignalMap.allSelection_labels]]
            exact ListIndex.get_eq
              ((rightSplitter element rightWidth).ports.outputs.labels.locate rightIndex) ▸
                List.get_mem _ _)
        (by
          intro member
          rcases List.mem_cons.mp member with equal | member
          · have childEqual := congrArg Certified.RuleOccurrence.child equal
            cases childEqual
          · have equal := List.mem_singleton.mp member
            have childEqual := congrArg Certified.RuleOccurrence.child equal
            cases childEqual)
        (.done (by
          intro output _
          cases output
          exact ⟨SignalComponentRule.apply, by simp,
            by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩))))

def stateSchedule (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.StateSchedule (body element leftWidth rightWidth)
      (children element leftWidth rightWidth) :=
  .done (by
    intro child input member
    cases child with
    | leftSplit =>
        change input ∈ (CycleStateRule.empty
          (leftSplitter element leftWidth).ports).readsInputs.labels at member
        exact nomatch member
    | rightSplit =>
        change input ∈ (CycleStateRule.empty
          (rightSplitter element rightWidth).ports).readsInputs.labels at member
        exact nomatch member
    | combine =>
        change input ∈ (CycleStateRule.empty
          (combiner element leftWidth rightWidth).ports).readsInputs.labels at member
        exact nomatch member)

def ruleSchedules (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleSchedules (body element leftWidth rightWidth)
      (children element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) where
  output | .apply => outputSchedule element leftWidth rightWidth
  state := stateSchedule element leftWidth rightWidth

theorem coversChildren (element : SignalType) (leftWidth rightWidth : Nat) :
    (ruleSchedules element leftWidth rightWidth).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (ruleSchedules element leftWidth rightWidth) .apply
  cases child with
  | leftSplit =>
      change SignalComponentRule at rule
      cases rule
      simp [ruleSchedules, outputSchedule, Certified.Schedule.finalAvailability]
  | rightSplit =>
      change SignalComponentRule at rule
      cases rule
      simp [ruleSchedules, outputSchedule, Certified.Schedule.finalAvailability]
  | combine =>
      change SignalComponentRule at rule
      cases rule
      simp [ruleSchedules, outputSchedule, Certified.Schedule.finalAvailability]

theorem structuralResultUnique (element : SignalType) (leftWidth rightWidth : Nat) :
    (moduleStructure element leftWidth rightWidth).HasAtMostOneSolution :=
  (ruleSchedules element leftWidth rightWidth).hasAtMostOneSolution
    (coversChildren element leftWidth rightWidth)

def leftInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (leftSplitter element leftWidth).ports.inputs.Values
  | .value => inputs .left

def rightInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (rightSplitter element rightWidth).ports.inputs.Values
  | .value => inputs .right

def combineInputs
    (left : ProposedValues (leftSplitter element leftWidth).certified.moduleStructure)
    (right : ProposedValues (rightSplitter element rightWidth).certified.moduleStructure) :
    (combiner element leftWidth rightWidth).ports.inputs.Values := fun index =>
  Fin.addCases (fun leftIndex => left.outputs leftIndex)
    (fun rightIndex => right.outputs rightIndex) index

theorem hasStructuralResult (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : (moduleStructure element leftWidth rightWidth).State) :
    ∃ proposal, (moduleStructure element leftWidth rightWidth).IsSolution
      inputs state proposal := by
  rcases (leftSplitter element leftWidth).certified.hasStructuralResult
      (leftInputs inputs) (state .leftSplit) with ⟨left, leftSatisfies⟩
  rcases (rightSplitter element rightWidth).certified.hasStructuralResult
      (rightInputs inputs) (state .rightSplit) with ⟨right, rightSatisfies⟩
  rcases (combiner element leftWidth rightWidth).certified.hasStructuralResult
      (combineInputs left right) (state .combine) with ⟨combined, combineSatisfies⟩
  let proposals : (child : Instance) →
      ProposedValues (Certified.childStructure
        (children element leftWidth rightWidth) child)
    | .leftSplit => left
    | .rightSplit => right
    | .combine => combined
  let outputs : (ports element leftWidth rightWidth).outputs.Values := fun
    | .result => combined.outputs .value
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | leftSplit =>
        change (leftSplitter element leftWidth).certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _ inputs
            proposals .leftSplit) (state .leftSplit) left
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .leftSplit = leftInputs inputs by
          funext input; cases input; rfl]
        exact leftSatisfies
    | rightSplit =>
        change (rightSplitter element rightWidth).certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _ inputs
            proposals .rightSplit) (state .rightSplit) right
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .rightSplit = rightInputs inputs by
          funext input; cases input; rfl]
        exact rightSatisfies
    | combine =>
        change (combiner element leftWidth rightWidth).certified.moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _ inputs
            proposals .combine) (state .combine) combined
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .combine = combineInputs left right by
          funext index
          refine Fin.addCases ?_ ?_ index
          · intro leftIndex
            simp [ProposedValues.childInputs, body, wiring, combineInputs,
              EndpointContext.instanceOutput, SignalSource.value, proposals]
          · intro rightIndex
            simp [ProposedValues.childInputs, body, wiring, combineInputs,
              EndpointContext.instanceOutput, SignalSource.value, proposals]]
        exact combineSatisfies

private theorem implements (element : SignalType) (leftWidth rightWidth : Nat) :
    Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have leftOutputs : (proposals .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues (leftInputs inputs) := by
    exact childSatisfies .leftSplit
  have rightOutputs : (proposals .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues (rightInputs inputs) := by
    exact childSatisfies .rightSplit
  have combineOutputs : (proposals .combine).outputs =
      (combiner element leftWidth rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .combine) := by
    exact childSatisfies .combine
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = concat (inputs .left) (inputs .right)
    rw [show outputs .result = (proposals .combine).outputs .value by
      exact boundary .result]
    rw [congrFun combineOutputs .value]
    rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
        inputs proposals .combine =
          combineInputs (proposals .leftSplit) (proposals .rightSplit) by
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro leftIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]
      · intro rightIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]]
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro leftIndex
      simp [combiner, SignalCombiner.outputValues, combineInputs, concat]
      rw [leftOutputs]
      rfl
    · intro rightIndex
      simp [combiner, SignalCombiner.outputValues, combineInputs, concat]
      rw [rightOutputs]
      rfl
  · rfl

def certification (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleCycleCertification (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := hasStructuralResult element leftWidth rightWidth
  structuralResultUnique := structuralResultUnique element leftWidth rightWidth
  implements := implements element leftWidth rightWidth

def certified (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleCycleCertified (ports element leftWidth rightWidth) :=
  (certification element leftWidth rightWidth).bundle

end Silean.Modules.VectorConcat

namespace Silean.Modules.VectorConcat.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.VectorConcat.ports element leftWidth rightWidth) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .left => .vector elementNaming
    | .right => .vector elementNaming
  outputTypes := fun | .result => .vector elementNaming

def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePortsNaming (Modules.VectorConcat.ports element leftWidth rightWidth) :=
  portsWithNaming element leftWidth rightWidth (.positional element)

def namingWith (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.VectorConcat.moduleStructure element leftWidth rightWidth) :=
  .composite
    ⟨"vector_concat", "structural",
      [.shape element, .natural leftWidth, .natural rightWidth]⟩
    (portsWithNaming element leftWidth rightWidth elementNaming)
    (fun
      | .leftSplit => "split_left"
      | .rightSplit => "split_right"
      | .combine => "combine")
    (fun
      | .leftSplit => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector leftWidth element) (.vector elementNaming)
      | .rightSplit => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector rightWidth element) (.vector elementNaming)
      | .combine => Silean.Naming.SignalAdapter.combinerWithNaming
          (.vector (leftWidth + rightWidth) element) (.vector elementNaming))

def naming (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleNaming (Modules.VectorConcat.moduleStructure element leftWidth rightWidth) :=
  namingWith element leftWidth rightWidth (.positional element)

def namedModule (element : SignalType) (leftWidth rightWidth : Nat) : NamedModule where
  ports := Modules.VectorConcat.ports element leftWidth rightWidth
  moduleStructure := Modules.VectorConcat.moduleStructure element leftWidth rightWidth
  naming := naming element leftWidth rightWidth

end Silean.Modules.VectorConcat.Naming
