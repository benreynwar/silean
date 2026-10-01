import PicoRV.Decoder.DecoderInstructionMatchGate
import PicoRV.Decoder.Internal.DecoderInstructionMatchGateStructure
import PicoRV.Decoder.Internal.DecoderInstructionMatchGateCorrespondence
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction

/-! Internal schedule and structural certification for one match gate. -/

namespace PicoRV.Decoder.InstructionMatch.MatchGate.Structure

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  classAndField := Silean.Primitives.andCertified.certification,
  qualifiedResult := Silean.Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .classAndField => Silean.Primitives.AndRule.apply,
    .qualifiedResult => Silean.Primitives.AndRule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements : Silean.Contracts.Cycle.ImplementsSolutions
    (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have first := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .classAndField).ruleHolds Silean.Primitives.AndRule.apply)
  normalize_child_hyp first unfolding wiring, context
  have result := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .qualifiedResult).ruleHolds Silean.Primitives.AndRule.apply)
  normalize_child_hyp result unfolding wiring, context
  have resolved := result.trans (apply₂_congr Bool.and first rfl)
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    exact (satisfies.1 .result).trans resolved
  · exact Subsingleton.elim _ _

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Decoder.InstructionMatch.MatchGate.Structure

namespace PicoRV.Decoder.InstructionMatch.MatchGate.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription
open Silean.Authoring.CircuitDescription.Description

theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports := by
  have corresponds := description_corresponds
  unfold Structure.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := Structure.instancePorts,
      wiring := Structure.wiring })
    (children := Structure.structuralChildren)
    corresponds Structure.certification

end PicoRV.Decoder.InstructionMatch.MatchGate.Internal
