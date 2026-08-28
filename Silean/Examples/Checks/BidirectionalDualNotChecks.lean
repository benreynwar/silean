import Silean.CertifiedSchedule
import Silean.Examples.Checks.HierarchicalDualNotCertificationChecks

namespace Silean.Examples.Checks.BidirectionalDualNot

open Silean
open Silean.Certified

inductive Instance
  | a
  | b
deriving Enumeration

@[reducible] def instances : Instances :=
  EnumeratedMap.of Instance fun
    | .a | .b => Examples.Fixtures.DualNot.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instances := instances

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instances where
  moduleOutput
    | .forward => context.instanceOutput .b .forward
    | .backward => context.instanceOutput .a .backward
  instanceInput
    | .a, .forward => context.moduleInput .forward
    | .a, .backward => context.instanceOutput .b .backward
    | .b, .forward => context.instanceOutput .a .forward
    | .b, .backward => context.moduleInput .backward

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

def children : Certified.Children body
  | .a | .b => Examples.Checks.HierarchicalDualNotCertification.dualNotCertified

def moduleStructure : ModuleStructure ports :=
  Certified.moduleStructure body children

def inputSelection : (input : Examples.Fixtures.DualNot.Input) →
    SignalSelection ports.inputs (.ofList [.bit])
  | .forward => ports.inputs.select .forward
  | .backward => ports.inputs.select .backward

def outputSelection : (output : Examples.Fixtures.DualNot.Output) →
    SignalSelection ports.outputs (.ofList [.bit])
  | .forward => ports.outputs.select .forward
  | .backward => ports.outputs.select .backward

def outputRule (input : Examples.Fixtures.DualNot.Input)
    (output : Examples.Fixtures.DualNot.Output) :
    CycleOutputRule ports emptySignalMap (.ofLists [.bit] [.bit]) where
  readsInputs := inputSelection input
  writesOutputs := outputSelection output
  target | (value, ()), _ => (value, ())

inductive Rule
  | forward
  | backward
deriving Enumeration

def cycleContract : ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, outputRule .forward .forward⟩
    | .backward => ⟨_, outputRule .backward .backward⟩
  stateRule := CycleStateRule.empty ports
  outputCoverage := by rfl

abbrev aForward : RuleOccurrence children := ⟨.a, .forward⟩
abbrev bForward : RuleOccurrence children := ⟨.b, .forward⟩
abbrev aBackward : RuleOccurrence children := ⟨.a, .backward⟩
abbrev bBackward : RuleOccurrence children := ⟨.b, .backward⟩

@[simp] theorem aForward_reads : aForward.reads = [.forward] := rfl
@[simp] theorem bForward_reads : bForward.reads = [.forward] := rfl
@[simp] theorem aForward_writes : aForward.writes = [.forward] := rfl
@[simp] theorem bForward_writes : bForward.writes = [.forward] := rfl
@[simp] theorem aBackward_reads : aBackward.reads = [.backward] := rfl
@[simp] theorem bBackward_reads : bBackward.reads = [.backward] := rfl
@[simp] theorem aBackward_writes : aBackward.writes = [.backward] := rfl
@[simp] theorem bBackward_writes : bBackward.writes = [.backward] := rfl

def forwardSchedule : OutputSchedule body children cycleContract .forward :=
  .call aForward
    (by intro input member
        cases input with
        | forward => exact member
        | backward => simp at member)
    (by simp)
  (.call bForward
    (by intro input member
        cases input with
        | forward => exact ⟨.forward, by simp, by simp⟩
        | backward => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | forward => exact ⟨.forward, by simp, by simp⟩
    | backward =>
        simp [cycleContract, outputRule, outputSelection, SignalMap.select,
          SignalSelection.labels] at member)))

def backwardSchedule : OutputSchedule body children cycleContract .backward :=
  .call bBackward
    (by intro input member
        cases input with
        | forward => simp at member
        | backward => exact member)
    (by simp)
  (.call aBackward
    (by intro input member
        cases input with
        | forward => simp at member
        | backward => exact ⟨.backward, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | forward =>
        simp [cycleContract, outputRule, outputSelection, SignalMap.select,
          SignalSelection.labels] at member
    | backward => exact ⟨.backward, by simp, by simp⟩)))

def stateSchedule : StateSchedule body children :=
  .done (by
    intro child input member
    cases child <;>
      simp [children, Examples.Checks.HierarchicalDualNotCertification.dualNotCertified,
        Examples.Fixtures.DualNot.cycleContract, Examples.Fixtures.DualNot.stateRule,
        CycleStateRule.empty, SignalSelection.labels] at member)

def ruleSchedules : RuleSchedules body children cycleContract where
  output
    | .forward => forwardSchedule
    | .backward => backwardSchedule
  state := stateSchedule

theorem coversChildren : ruleSchedules.CoversChildren := by
  intro child rule
  cases child <;> cases rule
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .forward
    change aForward ∈ forwardSchedule.finalAvailability
    simp [forwardSchedule, Schedule.finalAvailability]
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .backward
    change aBackward ∈ backwardSchedule.finalAvailability
    simp [backwardSchedule, Schedule.finalAvailability]
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .forward
    change bForward ∈ forwardSchedule.finalAvailability
    simp [forwardSchedule, Schedule.finalAvailability]
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .backward
    change bBackward ∈ backwardSchedule.finalAvailability
    simp [backwardSchedule, Schedule.finalAvailability]

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

private theorem certifiedForward
    (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (currentState : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State)
    (proposal : ProposedValues Examples.Fixtures.HierarchicalDualNot.moduleStructure)
    (satisfies : Examples.Fixtures.HierarchicalDualNot.moduleStructure.IsSolution
      inputs currentState proposal) :
    proposal.outputs .forward = !inputs .forward := by
  let certified := Examples.Checks.HierarchicalDualNotCertification.dualNotCertified
  rcases certified.hasCorrespondingState currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements inputs contractState currentState proposal
      corresponds satisfies with ⟨nextState, evaluates, nextCorresponds⟩
  have holds := evaluates.1 Examples.Fixtures.DualNot.Rule.forward
  change Examples.Fixtures.DualNot.forwardRule.Holds inputs contractState
    proposal.outputs at holds
  simpa [Examples.Fixtures.DualNot.forwardRule, CycleOutputRule.Holds,
    SignalSelection.project, SignalSelection.Matches, SignalMap.select] using holds

private theorem certifiedBackward
    (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (currentState : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State)
    (proposal : ProposedValues Examples.Fixtures.HierarchicalDualNot.moduleStructure)
    (satisfies : Examples.Fixtures.HierarchicalDualNot.moduleStructure.IsSolution
      inputs currentState proposal) :
    proposal.outputs .backward = !inputs .backward := by
  let certified := Examples.Checks.HierarchicalDualNotCertification.dualNotCertified
  rcases certified.hasCorrespondingState currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements inputs contractState currentState proposal
      corresponds satisfies with ⟨nextState, evaluates, nextCorresponds⟩
  have holds := evaluates.1 Examples.Fixtures.DualNot.Rule.backward
  change Examples.Fixtures.DualNot.backwardRule.Holds inputs contractState
    proposal.outputs at holds
  simpa [Examples.Fixtures.DualNot.backwardRule, CycleOutputRule.Holds,
    SignalSelection.project, SignalSelection.Matches, SignalMap.select] using holds

def aInputs (inputs : ports.inputs.Values) :
    Examples.Fixtures.DualNot.ports.inputs.Values
  | .forward => inputs .forward
  | .backward => !inputs .backward

def bInputs (inputs : ports.inputs.Values) :
    Examples.Fixtures.DualNot.ports.inputs.Values
  | .forward => !inputs .forward
  | .backward => inputs .backward

theorem hasStructuralResult (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal := by
  rcases (children .a).hasStructuralResult (aInputs inputs) (currentState .a) with
    ⟨aProposal, aSatisfies⟩
  rcases (children .b).hasStructuralResult (bInputs inputs) (currentState .b) with
    ⟨bProposal, bSatisfies⟩
  have aForwardValue := certifiedForward (aInputs inputs) (currentState .a)
    aProposal aSatisfies
  have aBackwardValue := certifiedBackward (aInputs inputs) (currentState .a)
    aProposal aSatisfies
  have bForwardValue := certifiedForward (bInputs inputs) (currentState .b)
    bProposal bSatisfies
  have bBackwardValue := certifiedBackward (bInputs inputs) (currentState .b)
    bProposal bSatisfies
  change (aProposal.outputs .forward : Bool) =
    !((aInputs inputs) .forward : Bool) at aForwardValue
  change (aProposal.outputs .backward : Bool) =
    !((aInputs inputs) .backward : Bool) at aBackwardValue
  change (bProposal.outputs .forward : Bool) =
    !((bInputs inputs) .forward : Bool) at bForwardValue
  change (bProposal.outputs .backward : Bool) =
    !((bInputs inputs) .backward : Bool) at bBackwardValue
  have aForwardBit : (aProposal.outputs .forward : Bool) =
      !(inputs .forward : Bool) := by simpa [aInputs] using aForwardValue
  have aBackwardBit : (aProposal.outputs .backward : Bool) =
      (inputs .backward : Bool) := by simpa [aInputs] using aBackwardValue
  have bForwardBit : (bProposal.outputs .forward : Bool) =
      (inputs .forward : Bool) := by simpa [bInputs] using bForwardValue
  have bBackwardBit : (bProposal.outputs .backward : Bool) =
      !(inputs .backward : Bool) := by simpa [bInputs] using bBackwardValue
  let outputs : ports.outputs.Values := fun
    | .forward => inputs .forward
    | .backward => inputs .backward
  let childProposals : (name : Instance) → ProposedValues (childStructure children name)
    | .a => aProposal
    | .b => bProposal
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output
    cases output with
    | forward =>
        exact bForwardBit.symm
    | backward =>
        exact aBackwardBit.symm
  · intro child
    cases child with
    | a =>
        change (children .a).moduleStructure.IsSolution
          (ProposedValues.childInputs body (childStructure children) inputs
            childProposals .a) (currentState .a) aProposal
        rw [show ProposedValues.childInputs body (childStructure children) inputs
          childProposals .a = aInputs inputs by
            funext input
            cases input with
            | forward => rfl
            | backward =>
                change bProposal.outputs .backward = !inputs .backward
                exact bBackwardBit]
        exact aSatisfies
    | b =>
        change (children .b).moduleStructure.IsSolution
          (ProposedValues.childInputs body (childStructure children) inputs
            childProposals .b) (currentState .b) bProposal
        rw [show ProposedValues.childInputs body (childStructure children) inputs
          childProposals .b = bInputs inputs by
            funext input
            cases input with
            | forward =>
                change aProposal.outputs .forward = !inputs .forward
                exact aForwardBit
            | backward => rfl]
        exact bSatisfies

def stateCorresponds (_ : cycleContract.state.Values)
    (_ : moduleStructure.State) : Prop := True

theorem implements : Implements moduleStructure cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  let aActualInputs := ProposedValues.childInputs body (childStructure children)
    inputs childProposals .a
  let bActualInputs := ProposedValues.childInputs body (childStructure children)
    inputs childProposals .b
  have aForwardValue := certifiedForward aActualInputs (structuralState .a)
    (childProposals .a) (childSatisfies .a)
  have aBackwardValue := certifiedBackward aActualInputs (structuralState .a)
    (childProposals .a) (childSatisfies .a)
  have bForwardValue := certifiedForward bActualInputs (structuralState .b)
    (childProposals .b) (childSatisfies .b)
  have bBackwardValue := certifiedBackward bActualInputs (structuralState .b)
    (childProposals .b) (childSatisfies .b)
  change (childProposals .a).outputs .forward =
    !(inputs .forward : Bool) at aForwardValue
  change (childProposals .b).outputs .backward =
    !(inputs .backward : Bool) at bBackwardValue
  change (childProposals .b).outputs .forward =
    !((childProposals .a).outputs .forward : Bool) at bForwardValue
  change (childProposals .a).outputs .backward =
    !((childProposals .b).outputs .backward : Bool) at aBackwardValue
  have outputForward : outputs .forward = inputs .forward := by
    have atBoundary := boundary Examples.Fixtures.DualNot.Output.forward
    change outputs .forward = (childProposals .b).outputs .forward at atBoundary
    rw [atBoundary, bForwardValue, aForwardValue]
    cases inputs .forward <;> rfl
  have outputBackward : outputs .backward = inputs .backward := by
    have atBoundary := boundary Examples.Fixtures.DualNot.Output.backward
    change outputs .backward = (childProposals .a).outputs .backward at atBoundary
    rw [atBoundary, aBackwardValue, bBackwardValue]
    cases inputs .backward <;> rfl
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | forward =>
        simp only [cycleContract, outputRule, inputSelection, outputSelection,
          CycleOutputRule.Holds, SignalSelection.project,
          SignalSelection.Matches, SignalMap.select]
        constructor
        · simpa only [ProposedValues.outputs, moduleStructure,
            Certified.moduleStructure] using outputForward
        · trivial
    | backward =>
        simp only [cycleContract, outputRule, inputSelection, outputSelection,
          CycleOutputRule.Holds, SignalSelection.project,
          SignalSelection.Matches, SignalMap.select]
        constructor
        · simpa only [ProposedValues.outputs, moduleStructure,
            Certified.moduleStructure] using outputBackward
        · trivial
  · rfl

def certified : ModuleCycleCertified ports where
  moduleStructure := moduleStructure
  cycleContract := cycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := hasStructuralResult,
    structuralResultUnique := hasAtMostOneSolution,
    implements := implements }

theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other →
        other = proposal := by
  exact certified.hasExactlyOneStructuralResult inputs currentState

/-! Collapsing either child to one rule that reads both inputs would report a
cycle: initially `a` lacks its backward input and `b` lacks its forward input.
The two rule-local schedules above are therefore the material distinction. -/

def wholeChildReady : Instance → Availability children → Prop
  | .a, available => ∀ input,
      sourceAvailable (fun _ => True) available (body.wiring.instanceInput .a input)
  | .b, available => ∀ input,
      sourceAvailable (fun _ => True) available (body.wiring.instanceInput .b input)

theorem noWholeChildCanStart :
    ¬wholeChildReady .a [] ∧ ¬wholeChildReady .b [] := by
  constructor
  · intro ready
    have unavailable := ready Examples.Fixtures.DualNot.Input.backward
    change outputAvailable ([] : Availability children) .b .backward at unavailable
    rcases unavailable with ⟨rule, member, writes⟩
    cases member
  · intro ready
    have unavailable := ready Examples.Fixtures.DualNot.Input.forward
    change outputAvailable ([] : Availability children) .a .forward at unavailable
    rcases unavailable with ⟨rule, member, writes⟩
    cases member

end Silean.Examples.Checks.BidirectionalDualNot
