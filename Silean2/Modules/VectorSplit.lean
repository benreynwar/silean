import Silean2.CertifiedSchedule
import Silean2.Naming.SignalAdapterNaming
import Silean2.SignalAdapterCertified

namespace Silean2.Modules.VectorSplit

open Silean2

inductive Input | value
deriving Enumeration

inductive Output | left | right
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector (leftWidth + rightWidth) element

@[reducible] def outputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Output fun
    | .left => .vector leftWidth element
    | .right => .vector rightWidth element

@[reducible] def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePorts := ⟨inputMap element leftWidth rightWidth,
      outputMap element leftWidth rightWidth⟩

def leftPart (value : Fin (leftWidth + rightWidth) → α) : Fin leftWidth → α :=
  fun index => value (Fin.castAdd rightWidth index)

def rightPart (value : Fin (leftWidth + rightWidth) → α) : Fin rightWidth → α :=
  fun index => value (Fin.natAdd leftWidth index)

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    CycleOutputRule (ports element leftWidth rightWidth) emptySignalMap
      { inputTypes := .cons (.vector (leftWidth + rightWidth) element) .nil
        outputTypes := .cons (.vector leftWidth element)
          (.cons (.vector rightWidth element) .nil) } where
  readsInputs := (inputMap element leftWidth rightWidth).select .value
  writesOutputs := ((outputMap element leftWidth rightWidth).select .right).prepend .left
  target | (value, ()), _ => (leftPart value, (rightPart value, ()))

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
      outputs .left = leftPart (inputs .value) ∧
      outputs .right = rightPart (inputs .value) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .left = leftPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.1

theorem right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .right = rightPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.2

private def splitter (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalSplitter := .vector (leftWidth + rightWidth) element

private def leftCombiner (element : SignalType) (leftWidth : Nat) :
    SignalCombiner := .vector leftWidth element

private def rightCombiner (element : SignalType) (rightWidth : Nat) :
    SignalCombiner := .vector rightWidth element

inductive Instance | split | left | right
deriving Enumeration

@[reducible] def instances (element : SignalType) (leftWidth rightWidth : Nat) :
    Instances := EnumeratedMap.of Instance fun
  | .split => (splitter element leftWidth rightWidth).ports
  | .left => (leftCombiner element leftWidth).ports
  | .right => (rightCombiner element rightWidth).ports

@[reducible] def context (element : SignalType) (leftWidth rightWidth : Nat) :
    EndpointContext where
  ports := ports element leftWidth rightWidth
  instances := instances element leftWidth rightWidth

def wiring (element : SignalType) (leftWidth rightWidth : Nat) :
    Wiring (context element leftWidth rightWidth).ports
      (context element leftWidth rightWidth).instances where
  moduleOutput
    | .left => (context element leftWidth rightWidth).instanceOutput .left .value
    | .right => (context element leftWidth rightWidth).instanceOutput .right .value
  instanceInput
    | .split, .value => (context element leftWidth rightWidth).moduleInput .value
    | .left, index => (context element leftWidth rightWidth).instanceOutput
        .split (Fin.castAdd rightWidth index)
    | .right, index => (context element leftWidth rightWidth).instanceOutput
        .split (Fin.natAdd leftWidth index)

@[reducible] def body (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleBody := ⟨context element leftWidth rightWidth,
      wiring element leftWidth rightWidth⟩

@[reducible] def children (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.Children (body element leftWidth rightWidth)
  | .split => (splitter element leftWidth rightWidth).certified
  | .left => (leftCombiner element leftWidth).certified
  | .right => (rightCombiner element rightWidth).certified

def moduleStructure (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleStructure (ports element leftWidth rightWidth) :=
  Certified.moduleStructure (body element leftWidth rightWidth)
    (children element leftWidth rightWidth)

private abbrev splitOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.split, SignalComponentRule.apply⟩

private abbrev leftOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.left, SignalComponentRule.apply⟩

private abbrev rightOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.RuleOccurrence (children element leftWidth rightWidth) :=
  ⟨.right, SignalComponentRule.apply⟩

private theorem splitWrites (element : SignalType) (leftWidth rightWidth : Nat)
    (index : Fin (leftWidth + rightWidth)) :
    index ∈ (splitOccurrence element leftWidth rightWidth).writes := by
  change index ∈
    (splitter element leftWidth rightWidth).ports.outputs.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq
    ((splitter element leftWidth rightWidth).ports.outputs.labels.locate index) ▸
      List.get_mem _ _

def outputSchedule (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.OutputSchedule (body element leftWidth rightWidth)
      (children element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) .apply :=
  .call (splitOccurrence element leftWidth rightWidth)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, body, wiring, context,
        EndpointContext.moduleInput])
    (by simp)
    (.call (leftOccurrence element leftWidth rightWidth)
      (by intro index _; exact ⟨SignalComponentRule.apply, by simp,
        splitWrites element leftWidth rightWidth _⟩)
      (by simp)
      (.call (rightOccurrence element leftWidth rightWidth)
        (by intro index _; exact ⟨SignalComponentRule.apply, by simp,
          splitWrites element leftWidth rightWidth _⟩)
        (by simp)
        (.done (by
          intro output _
          cases output with
          | left => exact ⟨SignalComponentRule.apply, by simp,
              by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩
          | right => exact ⟨SignalComponentRule.apply, by simp,
              by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩))))

def stateSchedule (element : SignalType) (leftWidth rightWidth : Nat) :
    Certified.StateSchedule (body element leftWidth rightWidth)
      (children element leftWidth rightWidth) :=
  .done (by
    intro child input member
    cases child <;>
      change input ∈ (CycleStateRule.empty _).readsInputs.labels at member <;>
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
  | split | left | right =>
      change SignalComponentRule at rule
      cases rule
      simp [ruleSchedules, outputSchedule, Certified.Schedule.finalAvailability]

theorem structuralResultUnique (element : SignalType) (leftWidth rightWidth : Nat) :
    (moduleStructure element leftWidth rightWidth).HasAtMostOneSolution :=
  (ruleSchedules element leftWidth rightWidth).hasAtMostOneSolution
    (coversChildren element leftWidth rightWidth)

def splitInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (splitter element leftWidth rightWidth).ports.inputs.Values
  | .value => inputs .value

def leftInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (split : ProposedValues
      (splitter element leftWidth rightWidth).certified.moduleStructure) :
    (leftCombiner element leftWidth).ports.inputs.Values := fun index =>
  split.outputs (Fin.castAdd rightWidth index)

def rightInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (split : ProposedValues
      (splitter element leftWidth rightWidth).certified.moduleStructure) :
    (rightCombiner element rightWidth).ports.inputs.Values := fun index =>
  split.outputs (Fin.natAdd leftWidth index)

theorem hasStructuralResult (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : (moduleStructure element leftWidth rightWidth).State) :
    ∃ proposal, (moduleStructure element leftWidth rightWidth).IsSolution
      inputs state proposal := by
  rcases (children element leftWidth rightWidth .split).hasStructuralResult
      (splitInputs element leftWidth rightWidth inputs) (state .split) with
    ⟨split, splitSatisfies⟩
  rcases (children element leftWidth rightWidth .left).hasStructuralResult
      (leftInputs element leftWidth rightWidth split) (state .left) with
    ⟨left, leftSatisfies⟩
  rcases (children element leftWidth rightWidth .right).hasStructuralResult
      (rightInputs element leftWidth rightWidth split) (state .right) with
    ⟨right, rightSatisfies⟩
  let proposals : (child : Instance) →
      ProposedValues (Certified.childStructure
        (children element leftWidth rightWidth) child)
    | .split => split
    | .left => left
    | .right => right
  let outputs : (ports element leftWidth rightWidth).outputs.Values := fun
    | .left => left.outputs .value
    | .right => right.outputs .value
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | split =>
        change (children element leftWidth rightWidth .split).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .split) (state .split) split
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .split = splitInputs element leftWidth rightWidth inputs by
          funext input; cases input; rfl]
        exact splitSatisfies
    | left =>
        change (children element leftWidth rightWidth .left).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .left) (state .left) left
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .left = leftInputs element leftWidth rightWidth split by
          funext index; rfl]
        exact leftSatisfies
    | right =>
        change (children element leftWidth rightWidth .right).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .right) (state .right) right
        rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
            inputs proposals .right = rightInputs element leftWidth rightWidth split by
          funext index; rfl]
        exact rightSatisfies

private theorem implements (element : SignalType) (leftWidth rightWidth : Nat) :
    Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have splitOutputs : (proposals .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (splitInputs element leftWidth rightWidth inputs) := childSatisfies .split
  have leftOutputs : (proposals .left).outputs =
      (leftCombiner element leftWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .left) := childSatisfies .left
  have rightOutputs : (proposals .right).outputs =
      (rightCombiner element rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .right) := childSatisfies .right
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change outputs .left = leftPart (inputs .value)
      rw [show outputs .left = (proposals .left).outputs .value by
        exact boundary .left]
      rw [congrFun leftOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.castAdd rightWidth index) =
        inputs .value (Fin.castAdd rightWidth index)
      rw [splitOutputs]
      rfl
    · change outputs .right = rightPart (inputs .value)
      rw [show outputs .right = (proposals .right).outputs .value by
        exact boundary .right]
      rw [congrFun rightOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.natAdd leftWidth index) =
        inputs .value (Fin.natAdd leftWidth index)
      rw [splitOutputs]
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

end Silean2.Modules.VectorSplit

namespace Silean2.Modules.VectorSplit.Naming

open Silean2 Silean2.Naming

def portsWithNaming (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.VectorSplit.ports element leftWidth rightWidth) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .left => "left" | .right => "right"⟩
  inputTypes := fun | .value => .vector elementNaming
  outputTypes := fun | .left | .right => .vector elementNaming

def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePortsNaming (Modules.VectorSplit.ports element leftWidth rightWidth) :=
  portsWithNaming element leftWidth rightWidth (.positional element)

def namingWith (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.VectorSplit.moduleStructure element leftWidth rightWidth) :=
  .composite
    ⟨"vector_split", "structural",
      [.shape element, .natural leftWidth, .natural rightWidth]⟩
    (portsWithNaming element leftWidth rightWidth elementNaming)
    (fun | .split => "split" | .left => "combine_left" | .right => "combine_right")
    (fun
      | .split => Silean2.Naming.SignalAdapter.splitterWithNaming
          (.vector (leftWidth + rightWidth) element) (.vector elementNaming)
      | .left => Silean2.Naming.SignalAdapter.combinerWithNaming
          (.vector leftWidth element) (.vector elementNaming)
      | .right => Silean2.Naming.SignalAdapter.combinerWithNaming
          (.vector rightWidth element) (.vector elementNaming))

def naming (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleNaming (Modules.VectorSplit.moduleStructure element leftWidth rightWidth) :=
  namingWith element leftWidth rightWidth (.positional element)

def namedModule (element : SignalType) (leftWidth rightWidth : Nat) : NamedModule where
  ports := Modules.VectorSplit.ports element leftWidth rightWidth
  moduleStructure := Modules.VectorSplit.moduleStructure element leftWidth rightWidth
  naming := naming element leftWidth rightWidth

end Silean2.Modules.VectorSplit.Naming
