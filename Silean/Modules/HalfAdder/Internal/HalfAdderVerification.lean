import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.HalfAdder.HalfAdder
import Silean.Modules.HalfAdder.Internal.HalfAdderStructure
import Silean.Primitives.And
import Silean.Primitives.Xor

namespace Silean.Modules.HalfAdder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  sumGate := Primitives.xorCertified.certification,
  carryGate := Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .sum => [.sumGate => Primitives.XorRule.apply]
    | .carry => [.carryGate => Primitives.AndRule.apply]
  state := []

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (certificationStructure layerChildren) cycleContract
      (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have sumMatches := childMatch .sumGate
  have carryMatches := childMatch .carryGate
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
      change sumRule.Holds hierStep.inputs contractState hierStep.outputs
      have gateValue := (Primitives.xorOutputRule_holds_iff _ _ _).mp
        (sumMatches.ruleHolds Primitives.XorRule.apply)
      rw [sumRule_holds_iff]
      rw [show hierStep.outputs .sum =
          (hierStep.children .sumGate).outputs .output by
        exact boundary .sum]
      exact gateValue
    | carry =>
      change carryRule.Holds hierStep.inputs contractState hierStep.outputs
      have gateValue := (Primitives.andOutputRule_holds_iff _ _ _).mp
        (carryMatches.ruleHolds Primitives.AndRule.apply)
      rw [carryRule_holds_iff]
      rw [show hierStep.outputs .carry =
          (hierStep.children .carryGate).outputs .output by
        exact boundary .carry]
      exact gateValue
  · rfl

end LayerCertification

/-! The half-adder wiring implements its contract for every pair of child
structures implementing the XOR and AND boundary contracts. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Modules.HalfAdder

/-! ## Authored-description correspondence -/

namespace Silean.Modules.HalfAdder.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same : some description = ofNaming HalfAdder.naming := by
  rfl

private theorem unique : description.UniqueNames := by
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal <;> subst child <;>
    constructor <;> exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description HalfAdder.naming :=
  ⟨same, unique⟩

open Authoring.CircuitDescription.Description

/-- Generated proof of the implementation-independent claim exposed by the
public HalfAdder implementation facade. -/
theorem construction_correct :
    ImplementsCycleContract HalfAdder.description cycleContract Naming.ports := by
  have corresponds := description_corresponds
  unfold HalfAdder.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := { instancePorts := instancePorts, wiring := wiring })
    (children := structuralChildren)
    corresponds certification

end Silean.Modules.HalfAdder.Internal
