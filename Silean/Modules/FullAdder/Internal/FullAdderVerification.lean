import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.FullAdder.FullAdder
import Silean.Modules.HalfAdder.HalfAdderTheorems
import Silean.Primitives.Or

namespace Silean.Modules.FullAdder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

namespace Internal

/-- Proof that the concrete full-adder hierarchy contains no opaque leaves. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  ⟨rfl⟩

end Internal

/-! ## Cycle certification -/

module_child_certifications childContracts for body where
  operands := HalfAdder.certification,
  carry := HalfAdder.certification,
  combineCarry := Primitives.orCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .sum => [.operands => HalfAdder.Rule.sum,
      .carry => HalfAdder.Rule.sum]
    | .carryOut => [.operands => HalfAdder.Rule.sum,
      .operands => HalfAdder.Rule.carry,
      .carry => HalfAdder.Rule.carry,
      .combineCarry => Primitives.OrRule.apply]
  state := []

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have operandBehavior :=
    (childMatch .operands).boundaryFact HalfAdder.Behavior.of_allowed
  have operandSumValue := operandBehavior.sum
  have operandCarryValue := operandBehavior.carry
  have carryBehavior :=
    (childMatch .carry).boundaryFact HalfAdder.Behavior.of_allowed
  have finalSumValue := carryBehavior.sum
  have secondCarryValue := carryBehavior.carry
  have combinedCarryValue :=
    (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .combineCarry).ruleHolds Primitives.OrRule.apply)
  rcases hierStep with ⟨inputs, outputs, children⟩
  normalize_child_hyp operandSumValue unfolding wiring, context
  normalize_child_hyp operandCarryValue unfolding wiring, context
  normalize_child_hyp finalSumValue unfolding wiring, context
  normalize_child_hyp secondCarryValue unfolding wiring, context
  normalize_child_hyp combinedCarryValue unfolding wiring, context
  simp only [HierStep.inputs, HierStep.childOutputs, HierStep.children] at operandSumValue
  simp only [HierStep.inputs, HierStep.childOutputs, HierStep.children] at operandCarryValue
  simp only [HierStep.inputs, HierStep.childOutputs, HierStep.children] at finalSumValue
  simp only [HierStep.inputs, HierStep.childOutputs, HierStep.children] at secondCarryValue
  simp only [HierStep.childOutputs, HierStep.children] at combinedCarryValue
  have boundary := satisfies.1
  change HierStep.ParentOutputsSatisfy body inputs outputs
    (fun name => (children name).outputs) at boundary
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
        change sumRule.Holds inputs contractState outputs
        rw [sumRule_holds_iff]
        rw [show outputs .sum = (children .carry).outputs .sum by
          exact boundary .sum]
        change (children .carry).outputs .sum = _
        rw [finalSumValue]
        change HalfAdder.sumValue (children .operands |>.outputs .sum)
          (inputs .carryIn) = _
        rw [operandSumValue]
        rfl
    | carryOut =>
        change carryOutRule.Holds inputs contractState outputs
        rw [carryOutRule_holds_iff]
        rw [show outputs .carryOut =
            (children .combineCarry).outputs .output by
          exact boundary .carryOut]
        change (children .combineCarry).outputs .output = _
        rw [combinedCarryValue]
        change ((children .operands).outputs .carry ||
          (children .carry).outputs .carry) = _
        rw [operandCarryValue, secondCarryValue]
        change (HalfAdder.carryValue (inputs .left) (inputs .right) ||
          HalfAdder.carryValue (children .operands |>.outputs .sum)
            (inputs .carryIn)) = _
        rw [operandSumValue]
        cases inputs .left <;> cases inputs .right <;> cases inputs .carryIn <;>
          decide
  · rfl

end LayerCertification

/-! The full-adder wiring implements its contract for every family of child
structures implementing the two HalfAdder and OR boundary contracts. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

namespace Internal

/-- Proof-level bridge used by the reader-facing structural behavior theorem. -/
theorem behavior_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    Behavior step.inputs step.outputs := by
  obtain ⟨contractState, stateCorresponds⟩ :=
    certification.hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes
    contractState step stateCorresponds realizes
  exact Behavior.of_allowed allowed

end Internal

end Silean.Modules.FullAdder

/-! ## Authored-description correspondence -/

namespace Silean.Modules.FullAdder.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same : some description = ofNaming FullAdder.naming := by
  rfl

private theorem unique : description.UniqueNames := by
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal <;> subst child <;>
    constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description FullAdder.naming :=
  ⟨same, unique⟩

end Silean.Modules.FullAdder.Description.Internal
