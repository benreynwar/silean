import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Examples.Checks.HierarchicalDualNotCertificationChecks

namespace Silean.Examples.Checks.BidirectionalDualNot

open Silean
open Silean.Contracts.Cycle.Certification.Layer

inductive Instance
  | a
  | b
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .a | .b => Examples.Fixtures.DualNot.ports

@[reducible] def context : EndpointContext where
  ports := Examples.Fixtures.DualNot.ports
  instancePorts := instancePorts

@[reducible] def ports : ModulePorts := context.ports

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .forward => context.instanceOutput .b .forward
    | .backward => context.instanceOutput .a .backward
  instanceInput
    | .a, .forward => context.moduleInput .forward
    | .a, .backward => context.instanceOutput .b .backward
    | .b, .forward => context.instanceOutput .a .forward
    | .b, .backward => context.moduleInput .backward

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .a | .b => Examples.Fixtures.DualNot.cycleContract

def children : Contracts.Cycle.Certification.Layer.ChildStructures body childContracts
  | .a | .b =>
      Examples.Checks.HierarchicalDualNotCertification.dualNotCertified.certifiedStructure

def moduleStructure : ModuleStructure ports :=
  Contracts.Cycle.Certification.Layer.moduleStructure body children

@[reducible] def layerChildren := children

inductive Rule
  | forward
  | backward
deriving Enumeration

def outputRule : Rule → Contracts.Cycle.CycleOutputRule ports emptySignalMap
  | .forward =>
      { readsInputs := Examples.Fixtures.DualNot.ruleInput .forward
        writesOutputs := Examples.Fixtures.DualNot.ruleOutput .forward
        target := fun inputs _ => fun | .value => inputs .value }
  | .backward =>
      { readsInputs := Examples.Fixtures.DualNot.ruleInput .backward
        writesOutputs := Examples.Fixtures.DualNot.ruleOutput .backward
        target := fun inputs _ => fun | .value => inputs .value }

def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => outputRule .forward
    | .backward => outputRule .backward
  stateRule := Contracts.Cycle.CycleStateRule.empty ports
  outputCoverage := by rfl

abbrev aForward : RuleOccurrence body childContracts := ⟨.a, .forward⟩
abbrev bForward : RuleOccurrence body childContracts := ⟨.b, .forward⟩
abbrev aBackward : RuleOccurrence body childContracts := ⟨.a, .backward⟩
abbrev bBackward : RuleOccurrence body childContracts := ⟨.b, .backward⟩

def scheduleOrders : ScheduleDerivation.RuleScheduleOrders body childContracts cycleContract where
  output
    | .forward => [aForward, bForward]
    | .backward => [bBackward, aBackward]
  state := []

def derivedRuleSchedules :
    ScheduleDerivation.DerivedRuleSchedules body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

abbrev ruleSchedules := derivedRuleSchedules.schedules

theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren



theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren layerChildren

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
  exact (Examples.Fixtures.DualNot.forwardRule_holds_iff _ _ _).mp holds

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
  exact (Examples.Fixtures.DualNot.backwardRule_holds_iff _ _ _).mp holds

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
  rcases (children .a).certification.hasStructuralResult
      (aInputs inputs) (currentState .a) with
    ⟨aProposal, aSatisfies⟩
  rcases (children .b).certification.hasStructuralResult
      (bInputs inputs) (currentState .b) with
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
  let childProposals : (name : Instance) → ProposedValues
      ((fun name => (children name).moduleStructure) name)
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
          (ProposedValues.childInputs body
            ((fun name => (children name).moduleStructure)) inputs
            childProposals .a) (currentState .a) aProposal
        rw [show ProposedValues.childInputs body
          ((fun name => (children name).moduleStructure)) inputs
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
          (ProposedValues.childInputs body
            ((fun name => (children name).moduleStructure)) inputs
            childProposals .b) (currentState .b) bProposal
        rw [show ProposedValues.childInputs body
          ((fun name => (children name).moduleStructure)) inputs
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

theorem implements : Contracts.Cycle.Implements moduleStructure cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  let aActualInputs := ProposedValues.childInputs body
    ((fun name => (children name).moduleStructure))
    inputs childProposals .a
  let bActualInputs := ProposedValues.childInputs body
    ((fun name => (children name).moduleStructure))
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
        unfold cycleContract outputRule Contracts.Cycle.CycleOutputRule.Holds
          SignalGroup.Matches
        funext output
        cases output
        change outputs .forward = inputs .forward
        exact outputForward
    | backward =>
        unfold cycleContract outputRule Contracts.Cycle.CycleOutputRule.Holds
          SignalGroup.Matches
        funext output
        cases output
        change outputs .backward = inputs .backward
        exact outputBackward
  · rfl

def certified : Contracts.Cycle.ModuleCycleCertified ports where
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

def wholeChildReady : Instance → Availability body childContracts → Prop
  | .a, available => ∀ input,
      sourceAvailable (fun _ => True) available (body.wiring.instanceInput .a input)
  | .b, available => ∀ input,
      sourceAvailable (fun _ => True) available (body.wiring.instanceInput .b input)

theorem noWholeChildCanStart :
    ¬wholeChildReady .a [] ∧ ¬wholeChildReady .b [] := by
  constructor
  · intro ready
    have unavailable := ready Examples.Fixtures.DualNot.Input.backward
    change outputAvailable ([] : Availability body childContracts) .b .backward at unavailable
    rcases unavailable with ⟨rule, member, writes⟩
    cases member
  · intro ready
    have unavailable := ready Examples.Fixtures.DualNot.Input.forward
    change outputAvailable ([] : Availability body childContracts) .a .forward at unavailable
    rcases unavailable with ⟨rule, member, writes⟩
    cases member

end Silean.Examples.Checks.BidirectionalDualNot
