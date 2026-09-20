import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMux
import Silean.Modules.BitMux.Internal.BitMuxStructure
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Modules.BitMux

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  invertSelect := Primitives.notCertified.certification,
  chooseFalse := Primitives.andCertified.certification,
  chooseTrue := Primitives.andCertified.certification,
  combine := Primitives.orCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .select => [.invertSelect => Primitives.NotRule.apply,
      .chooseFalse => Primitives.AndRule.apply,
      .chooseTrue => Primitives.AndRule.apply,
      .combine => Primitives.OrRule.apply]
  state := []

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change selectRule.Holds hierStep.inputs contractState _
    have boundary' : hierStep.outputs .result =
        (hierStep.children .combine).outputs .output := by
      exact boundary .result
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .invertSelect).ruleHolds Primitives.NotRule.apply)
    have falseBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .chooseFalse).ruleHolds Primitives.AndRule.apply)
    have trueBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .chooseTrue).ruleHolds Primitives.AndRule.apply)
    have combineBit := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .combine).ruleHolds Primitives.OrRule.apply)
    change (hierStep.children .invertSelect).outputs .output =
      !hierStep.inputs .select at invertBit
    change (hierStep.children .chooseFalse).outputs .output =
      (hierStep.inputs .whenFalse &&
        (hierStep.children .invertSelect).outputs .output) at falseBit
    change (hierStep.children .chooseTrue).outputs .output =
      (hierStep.inputs .whenTrue && hierStep.inputs .select) at trueBit
    change (hierStep.children .combine).outputs .output =
      ((hierStep.children .chooseFalse).outputs .output ||
        (hierStep.children .chooseTrue).outputs .output) at combineBit
    rw [selectRule_holds_iff]
    change hierStep.outputs .result =
      bif hierStep.inputs .select then hierStep.inputs .whenTrue
      else hierStep.inputs .whenFalse
    rw [boundary', combineBit, falseBit, trueBit, invertBit]
    cases hierStep.inputs .select <;> cases hierStep.inputs .whenFalse <;>
      cases hierStep.inputs .whenTrue <;> rfl
  · rfl

end LayerCertification

/- The gate-level mux wiring implements its contract using only the public
contracts of its primitive children. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Modules.BitMux

/-! ## Authored-description correspondence -/

namespace Silean.Modules.BitMux.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same : some description = ofNaming BitMux.naming := by
  rfl

theorem description_corresponds : Corresponds description BitMux.naming :=
  ⟨same⟩

open Authoring.CircuitDescription.Description

/-- Generated proof of the implementation-independent claim exposed by the
public bit-mux facade. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports := by
  have corresponds := description_corresponds
  unfold BitMux.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := { instancePorts := instancePorts, wiring := wiring })
    (children := structuralChildren)
    corresponds certification

end Silean.Modules.BitMux.Internal
