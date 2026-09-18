import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Examples.Fixtures.DualNot
import Silean.Examples.Fixtures.HierarchicalDualNot

namespace Silean.Examples.Checks.HierarchicalDualNotCertification

open Silean
open Silean.Contracts.Cycle.Certification.Layer

private abbrev childContracts :=
  Examples.Fixtures.HierarchicalDualNot.childContracts

private abbrev layerChildren :=
  Examples.Fixtures.HierarchicalDualNot.children

private def stateCorresponds (_ : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (_ : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions Examples.Fixtures.HierarchicalDualNot.moduleStructure
    Examples.Fixtures.DualNot.cycleContract stateCorresponds := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatches for
    Examples.Fixtures.HierarchicalDualNot.body from
      layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    · change Examples.Fixtures.DualNot.forwardRule.Holds
        hierStep.inputs contractState _
      rw [Examples.Fixtures.DualNot.forwardRule_holds_iff]
      have childOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
        ((childMatches .forwardNot).ruleHolds Primitives.NotRule.apply)
      normalize_child_hyp childOutput unfolding
        Examples.Fixtures.HierarchicalDualNot.wiring,
        Examples.Fixtures.HierarchicalDualNot.context
      exact (boundary .forward).trans childOutput
    · change Examples.Fixtures.DualNot.backwardRule.Holds
        hierStep.inputs contractState _
      rw [Examples.Fixtures.DualNot.backwardRule_holds_iff]
      have childOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
        ((childMatches .backwardNot).ruleHolds Primitives.NotRule.apply)
      normalize_child_hyp childOutput unfolding
        Examples.Fixtures.HierarchicalDualNot.wiring,
        Examples.Fixtures.HierarchicalDualNot.context
      exact (boundary .backward).trans childOutput
  · rfl

abbrev forwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.forwardNot, Primitives.NotRule.apply⟩

abbrev backwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.backwardNot, Primitives.NotRule.apply⟩

def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    Examples.Fixtures.HierarchicalDualNot.body childContracts
    Examples.Fixtures.DualNot.cycleContract where
  output
    | .forward => [forwardOccurrence]
    | .backward => [backwardOccurrence]
  state := []

def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    Examples.Fixtures.HierarchicalDualNot.body childContracts
    Examples.Fixtures.DualNot.cycleContract := by
  derive_rule_schedules scheduleOrders

abbrev ruleSchedules := derivedRuleSchedules.schedules

theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren



theorem hasAtMostOneSolution :
    Examples.Fixtures.HierarchicalDualNot.moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren layerChildren

def dualNotCertified : Contracts.Cycle.ModuleCycleCertified Examples.Fixtures.DualNot.ports where
  moduleStructure := Examples.Fixtures.HierarchicalDualNot.moduleStructure
  cycleContract := Examples.Fixtures.DualNot.cycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := ruleSchedules.hasSolution coversChildren layerChildren,
    structuralResultUnique := hasAtMostOneSolution,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp implements }

end Silean.Examples.Checks.HierarchicalDualNotCertification
