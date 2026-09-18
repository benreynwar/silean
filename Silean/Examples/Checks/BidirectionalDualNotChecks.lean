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

def stateCorresponds (_ : cycleContract.state.Values)
    (_ : moduleStructure.State) : Prop := True

theorem implements : Contracts.Cycle.ImplementsSolutions moduleStructure cycleContract stateCorresponds := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatches for body from
    layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  have aForwardValue :=
    (Examples.Fixtures.DualNot.forwardRule_holds_iff _ _ _).mp
      ((childMatches .a).ruleHolds .forward)
  have aBackwardValue :=
    (Examples.Fixtures.DualNot.backwardRule_holds_iff _ _ _).mp
      ((childMatches .a).ruleHolds .backward)
  have bForwardValue :=
    (Examples.Fixtures.DualNot.forwardRule_holds_iff _ _ _).mp
      ((childMatches .b).ruleHolds .forward)
  have bBackwardValue :=
    (Examples.Fixtures.DualNot.backwardRule_holds_iff _ _ _).mp
      ((childMatches .b).ruleHolds .backward)
  normalize_child_hyp aForwardValue unfolding wiring, context
  normalize_child_hyp aBackwardValue unfolding wiring, context
  normalize_child_hyp bForwardValue unfolding wiring, context
  normalize_child_hyp bBackwardValue unfolding wiring, context
  have outputForward : (hierStep.outputs .forward : Bool) =
      (hierStep.inputs .forward : Bool) := by
    have atBoundary := boundary Examples.Fixtures.DualNot.Output.forward
    normalize_child_hyp atBoundary unfolding wiring, context
    have doubleNegation : Bool.not (Bool.not (hierStep.inputs .forward : Bool)) =
        (hierStep.inputs .forward : Bool) := by
      cases hierStep.inputs .forward <;> rfl
    exact atBoundary.trans (bForwardValue.trans
      ((congrArg Bool.not aForwardValue).trans
        doubleNegation))
  have outputBackward : (hierStep.outputs .backward : Bool) =
      (hierStep.inputs .backward : Bool) := by
    have atBoundary := boundary Examples.Fixtures.DualNot.Output.backward
    normalize_child_hyp atBoundary unfolding wiring, context
    have doubleNegation : Bool.not (Bool.not (hierStep.inputs .backward : Bool)) =
        (hierStep.inputs .backward : Bool) := by
      cases hierStep.inputs .backward <;> rfl
    exact atBoundary.trans (aBackwardValue.trans
      ((congrArg Bool.not bBackwardValue).trans
        doubleNegation))
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | forward =>
        unfold cycleContract outputRule Contracts.Cycle.CycleOutputRule.Holds
          SignalGroup.Matches
        funext output
        cases output
        change hierStep.outputs .forward = hierStep.inputs .forward
        exact outputForward
    | backward =>
        unfold cycleContract outputRule Contracts.Cycle.CycleOutputRule.Holds
          SignalGroup.Matches
        funext output
        cases output
        change hierStep.outputs .backward = hierStep.inputs .backward
        exact outputBackward
  · rfl

def certified : Contracts.Cycle.ModuleCycleCertified ports where
  moduleStructure := moduleStructure
  cycleContract := cycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := ruleSchedules.hasSolution coversChildren layerChildren,
    structuralResultUnique := hasAtMostOneSolution,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp implements }

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨ruleSchedules.hasSolution coversChildren layerChildren,
    hasAtMostOneSolution⟩

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
