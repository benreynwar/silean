import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import SileanTests.Fixtures.DualNot
import SileanTests.Fixtures.HierarchicalDualNot

namespace SileanTests.HierarchicalDualNotCertification

open Silean
open Silean.Contracts.Cycle.Certification.Layer

private abbrev childContracts :=
  SileanTests.Fixtures.HierarchicalDualNot.childContracts

private abbrev layerChildren :=
  SileanTests.Fixtures.HierarchicalDualNot.children

private def stateCorresponds (_ : SileanTests.Fixtures.DualNot.cycleContract.state.Values)
    (_ : SileanTests.Fixtures.HierarchicalDualNot.moduleStructure.State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions SileanTests.Fixtures.HierarchicalDualNot.moduleStructure
    SileanTests.Fixtures.DualNot.cycleContract stateCorresponds := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatches for
    SileanTests.Fixtures.HierarchicalDualNot.body from
      layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    · change SileanTests.Fixtures.DualNot.forwardRule.Holds
        hierStep.inputs contractState _
      rw [SileanTests.Fixtures.DualNot.forwardRule_holds_iff]
      have childOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
        ((childMatches .forwardNot).ruleHolds Primitives.NotRule.apply)
      normalize_child_hyp childOutput unfolding
        SileanTests.Fixtures.HierarchicalDualNot.wiring,
        SileanTests.Fixtures.HierarchicalDualNot.context
      exact (boundary .forward).trans childOutput
    · change SileanTests.Fixtures.DualNot.backwardRule.Holds
        hierStep.inputs contractState _
      rw [SileanTests.Fixtures.DualNot.backwardRule_holds_iff]
      have childOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
        ((childMatches .backwardNot).ruleHolds Primitives.NotRule.apply)
      normalize_child_hyp childOutput unfolding
        SileanTests.Fixtures.HierarchicalDualNot.wiring,
        SileanTests.Fixtures.HierarchicalDualNot.context
      exact (boundary .backward).trans childOutput
  · rfl

abbrev forwardOccurrence :
    RuleOccurrence SileanTests.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨SileanTests.Fixtures.HierarchicalDualNot.Instance.forwardNot, Primitives.NotRule.apply⟩

abbrev backwardOccurrence :
    RuleOccurrence SileanTests.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨SileanTests.Fixtures.HierarchicalDualNot.Instance.backwardNot, Primitives.NotRule.apply⟩

def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    SileanTests.Fixtures.HierarchicalDualNot.body childContracts
    SileanTests.Fixtures.DualNot.cycleContract where
  output
    | .forward => [forwardOccurrence]
    | .backward => [backwardOccurrence]
  state := []

def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    SileanTests.Fixtures.HierarchicalDualNot.body childContracts
    SileanTests.Fixtures.DualNot.cycleContract := by
  derive_rule_schedules scheduleOrders

abbrev ruleSchedules := derivedRuleSchedules.schedules

theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

theorem structuralCertification :
    ModuleStructuralCertification
      SileanTests.Fixtures.HierarchicalDualNot.moduleStructure :=
  ruleSchedules.structuralCertification coversChildren layerChildren

theorem hasAtMostOneSolution :
    SileanTests.Fixtures.HierarchicalDualNot.moduleStructure.HasAtMostOneSolution :=
  structuralCertification.hasAtMostOneSolution

def dualNotCertified : Contracts.Cycle.ModuleCycleCertified SileanTests.Fixtures.DualNot.ports where
  moduleStructure := SileanTests.Fixtures.HierarchicalDualNot.moduleStructure
  cycleContract := SileanTests.Fixtures.DualNot.cycleContract
  certification := {
    structural := structuralCertification
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp implements }

end SileanTests.HierarchicalDualNotCertification
