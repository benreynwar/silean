import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.FullAdder.Internal.FullAdderStructure
import Silean.Modules.HalfAdder.HalfAdderDerived
import Silean.Primitives.Or

namespace Silean.Modules.FullAdder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

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
  have operandSumValue :=
    (childMatch .operands).boundaryOutput HalfAdder.cycleContract.sumEquation
  have operandCarryValue :=
    (childMatch .operands).boundaryOutput HalfAdder.cycleContract.carryEquation
  have finalSumValue :=
    (childMatch .carry).boundaryOutput HalfAdder.cycleContract.sumEquation
  have secondCarryValue :=
    (childMatch .carry).boundaryOutput HalfAdder.cycleContract.carryEquation
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

end Silean.Modules.FullAdder

/-! ## Authored-description correspondence -/

namespace Silean.Modules.FullAdder.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same : some description = ofNaming FullAdder.naming := by
  rfl

theorem description_corresponds : Corresponds description FullAdder.naming :=
  ⟨same⟩

open Authoring.CircuitDescription.Description

/-- Generated proof of the implementation-independent claim exposed by the
public FullAdder implementation facade. -/
theorem construction_correct :
    ImplementsCycleContract FullAdder.description cycleContract Naming.ports := by
  have corresponds := description_corresponds
  unfold FullAdder.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := { instancePorts := instancePorts, wiring := wiring })
    (children := structuralChildren)
    corresponds certification

end Silean.Modules.FullAdder.Internal
