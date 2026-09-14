import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummaryStructure
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Any.Any
import Silean.Primitives.Not

namespace Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

noncomputable section

set_option maxHeartbeats 2000000

module_child_certifications childContracts for body where
  recognized := Modules.Any.certification 38,
  trap := Primitives.notCertified.certification,
  luiAuipcJal := Modules.Any.certification 3,
  arithmetic := Modules.Any.certification 7,
  signedCompare := Modules.Any.certification 3,
  unsignedCompare := Modules.Any.certification 3,
  unsignedLoad := Modules.Any.certification 3,
  compare := Modules.Any.certification 5

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .trap => [
        .recognized => Modules.Any.Rule.apply,
        .trap => Primitives.NotRule.apply]
    | .summaries => [
        .luiAuipcJal => Modules.Any.Rule.apply,
        .arithmetic => Modules.Any.Rule.apply,
        .signedCompare => Modules.Any.Rule.apply,
        .unsignedCompare => Modules.Any.Rule.apply,
        .unsignedLoad => Modules.Any.Rule.apply,
        .compare => Modules.Any.Rule.apply]
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

  have recognizedValue : (proposal.2 .recognized).outputs .output =
      recognized (valuesOf inputs) := by
    have equation := (Modules.Any.outputRule_holds_iff_width 38 _ _ _).mp
      ((childMatch .recognized).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      recognized, valuesOf, matchedValues, boolOr, List.any] using equation
  have trapValue : (proposal.2 .trap).outputs .output =
      outputValues (valuesOf inputs) .instr_trap := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .trap).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [recognizedValue] at equation
    simpa [outputValues] using equation

  have luiAuipcJalValue : (proposal.2 .luiAuipcJal).outputs .output =
      outputValues (valuesOf inputs) .is_lui_auipc_jal := by
    have equation := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .luiAuipcJal).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, boolOr, List.any] using equation
  have arithmeticValue : (proposal.2 .arithmetic).outputs .output =
      outputValues (valuesOf inputs) .is_lui_auipc_jal_jalr_addi_add_sub := by
    have equation := (Modules.Any.outputRule_holds_iff_width 7 _ _ _).mp
      ((childMatch .arithmetic).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, matchedValues, boolOr, List.any] using equation
  have signedCompareValue : (proposal.2 .signedCompare).outputs .output =
      outputValues (valuesOf inputs) .is_slti_blt_slt := by
    have equation := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .signedCompare).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, matchedValues, boolOr, List.any] using equation
  have unsignedCompareValue : (proposal.2 .unsignedCompare).outputs .output =
      outputValues (valuesOf inputs) .is_sltiu_bltu_sltu := by
    have equation := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedCompare).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, matchedValues, boolOr, List.any] using equation
  have unsignedLoadValue : (proposal.2 .unsignedLoad).outputs .output =
      outputValues (valuesOf inputs) .is_lbu_lhu_lw := by
    have equation := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedLoad).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, matchedValues, boolOr, List.any] using equation
  have compareValue : (proposal.2 .compare).outputs .output =
      outputValues (valuesOf inputs) .is_compare := by
    have equation := (Modules.Any.outputRule_holds_iff_width 5 _ _ _).mp
      ((childMatch .compare).1.1 Modules.Any.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Modules.Any.some_zero, Modules.Any.some_succ, Modules.Any.input,
      outputValues, valuesOf, matchedValues, boolOr, List.any] using equation

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | trap =>
      rw [trapOutputRule_holds_iff]
      rw [show proposal.outputs .instr_trap =
        (proposal.2 .trap).outputs .output by exact boundary _]
      exact trapValue
    | summaries =>
      rw [summariesOutputRule_holds_iff]
      intro output notTrap
      cases output with
      | instr_trap => contradiction
      | is_lui_auipc_jal =>
        rw [show proposal.outputs .is_lui_auipc_jal =
          (proposal.2 .luiAuipcJal).outputs .output by exact boundary _]
        exact luiAuipcJalValue
      | is_lui_auipc_jal_jalr_addi_add_sub =>
        rw [show proposal.outputs .is_lui_auipc_jal_jalr_addi_add_sub =
          (proposal.2 .arithmetic).outputs .output by exact boundary _]
        exact arithmeticValue
      | is_slti_blt_slt =>
        rw [show proposal.outputs .is_slti_blt_slt =
          (proposal.2 .signedCompare).outputs .output by exact boundary _]
        exact signedCompareValue
      | is_sltiu_bltu_sltu =>
        rw [show proposal.outputs .is_sltiu_bltu_sltu =
          (proposal.2 .unsignedCompare).outputs .output by exact boundary _]
        exact unsignedCompareValue
      | is_lbu_lhu_lw =>
        rw [show proposal.outputs .is_lbu_lhu_lw =
          (proposal.2 .unsignedLoad).outputs .output by exact boundary _]
        exact unsignedLoadValue
      | is_compare =>
        rw [show proposal.outputs .is_compare =
          (proposal.2 .compare).outputs .output by exact boundary _]
        exact compareValue
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

end

end Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure
