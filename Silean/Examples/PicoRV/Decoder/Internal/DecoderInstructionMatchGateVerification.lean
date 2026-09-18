import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchGate
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction

/-! Internal schedule and structural certification for one match gate. -/

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate.Structure

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  classAndField := Primitives.andCertified.certification,
  qualifiedResult := Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .classAndField => Primitives.AndRule.apply,
    .qualifiedResult => Primitives.AndRule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have first := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .classAndField).ruleHolds Primitives.AndRule.apply)
  normalize_child_hyp first unfolding wiring, context
  have result := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .qualifiedResult).ruleHolds Primitives.AndRule.apply)
  normalize_child_hyp result unfolding wiring, context
  have resolved := result.trans (apply₂_congr Bool.and first rfl)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate.Structure
