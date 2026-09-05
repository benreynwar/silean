import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.HalfAdder.HalfAdder
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
    Contracts.Cycle.Implements
      (certificationStructure layerChildren) cycleContract
      (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have sumMatches := childMatch .sumGate
  have carryMatches := childMatch .carryGate
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
      change sumRule.Holds inputs contractState _
      have gateValue := (Primitives.xorOutputRule_holds_iff _ _ _).mp
        (sumMatches.1.1 Primitives.XorRule.apply)
      rw [sumRule_holds_iff]
      rw [show proposal.outputs .sum = (proposal.2 .sumGate).outputs .output by
        exact boundary .sum]
      exact gateValue
    | carry =>
      change carryRule.Holds inputs contractState _
      have gateValue := (Primitives.andOutputRule_holds_iff _ _ _).mp
        (carryMatches.1.1 Primitives.AndRule.apply)
      rw [carryRule_holds_iff]
      rw [show proposal.outputs .carry = (proposal.2 .carryGate).outputs .output by
        exact boundary .carry]
      exact gateValue
  · rfl

end LayerCertification

/-- The half-adder hierarchy contains no behavioral blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  ⟨rfl⟩

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
