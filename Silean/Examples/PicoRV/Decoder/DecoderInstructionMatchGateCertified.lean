import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchGate
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction

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

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have first := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .classAndField).1.1 Primitives.AndRule.apply)
  normalize_child_hyp first unfolding body, wiring, context
  have result := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .qualifiedResult).1.1 Primitives.AndRule.apply)
  normalize_child_hyp result unfolding body, wiring, context
  rw [first] at result
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .result =
      (proposal.2 .qualifiedResult).outputs .output by
      exact satisfies.1 .result]
    exact result
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

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate.Structure
