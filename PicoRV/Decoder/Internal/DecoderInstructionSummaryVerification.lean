import PicoRV.Decoder.Internal.DecoderInstructionSummaryStructure
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Any.Any
import Silean.Primitives.Not

/-! Internal schedules and structural certification for instruction summaries. -/

namespace PicoRV.Decoder.InstructionSummary.Structure

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

noncomputable section

module_child_certifications childContracts for body where
  recognized := Silean.Modules.Any.certification 38,
  trap := Silean.Primitives.notCertified.certification,
  luiAuipcJal := Silean.Modules.Any.certification 3,
  arithmetic := Silean.Modules.Any.certification 7,
  signedCompare := Silean.Modules.Any.certification 3,
  unsignedCompare := Silean.Modules.Any.certification 3,
  unsignedLoad := Silean.Modules.Any.certification 3,
  compare := Silean.Modules.Any.certification 5

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .trap => [
        .recognized => Silean.Modules.Any.Rule.apply,
        .trap => Silean.Primitives.NotRule.apply]
    | .summaries => [
        .luiAuipcJal => Silean.Modules.Any.Rule.apply,
        .arithmetic => Silean.Modules.Any.Rule.apply,
        .signedCompare => Silean.Modules.Any.Rule.apply,
        .unsignedCompare => Silean.Modules.Any.Rule.apply,
        .unsignedLoad => Silean.Modules.Any.Rule.apply,
        .compare => Silean.Modules.Any.Rule.apply]
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

  have recognizedValue := (Silean.Modules.Any.outputRule_holds_iff_width 38 _ _ _).mp
      ((childMatch .recognized).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp recognizedValue unfolding wiring, context
  change hierStep.childOutputs .recognized .output =
    recognized (valuesOf hierStep.inputs) at recognizedValue
  have trapValue : hierStep.childOutputs .trap .output =
      outputValues (valuesOf hierStep.inputs) .instr_trap := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .trap).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact (equation.trans (congrArg Bool.not recognizedValue)).trans <| by
      rfl

  have luiAuipcJalValue := (Silean.Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .luiAuipcJal).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp luiAuipcJalValue unfolding wiring, context
  change hierStep.childOutputs .luiAuipcJal .output =
    outputValues (valuesOf hierStep.inputs) .is_lui_auipc_jal at luiAuipcJalValue
  have arithmeticValue := (Silean.Modules.Any.outputRule_holds_iff_width 7 _ _ _).mp
      ((childMatch .arithmetic).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp arithmeticValue unfolding wiring, context
  change hierStep.childOutputs .arithmetic .output =
    outputValues (valuesOf hierStep.inputs) .is_lui_auipc_jal_jalr_addi_add_sub
    at arithmeticValue
  have signedCompareValue := (Silean.Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .signedCompare).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp signedCompareValue unfolding wiring, context
  change hierStep.childOutputs .signedCompare .output =
    outputValues (valuesOf hierStep.inputs) .is_slti_blt_slt at signedCompareValue
  have unsignedCompareValue := (Silean.Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedCompare).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp unsignedCompareValue unfolding wiring, context
  change hierStep.childOutputs .unsignedCompare .output =
    outputValues (valuesOf hierStep.inputs) .is_sltiu_bltu_sltu at unsignedCompareValue
  have unsignedLoadValue := (Silean.Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedLoad).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp unsignedLoadValue unfolding wiring, context
  change hierStep.childOutputs .unsignedLoad .output =
    outputValues (valuesOf hierStep.inputs) .is_lbu_lhu_lw at unsignedLoadValue
  have compareValue := (Silean.Modules.Any.outputRule_holds_iff_width 5 _ _ _).mp
      ((childMatch .compare).ruleHolds Silean.Modules.Any.Rule.apply)
  normalize_child_hyp compareValue unfolding wiring, context
  change hierStep.childOutputs .compare .output =
    outputValues (valuesOf hierStep.inputs) .is_compare at compareValue

  have boundary := satisfies.1
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    dsimp only
    cases rule with
    | trap =>
      rw [trapOutputRule_holds_iff]
      exact (boundary _).trans trapValue
    | summaries =>
      rw [summariesOutputRule_holds_iff]
      intro output notTrap
      cases output with
      | instr_trap => contradiction
      | is_lui_auipc_jal =>
        exact (boundary _).trans luiAuipcJalValue
      | is_lui_auipc_jal_jalr_addi_add_sub =>
        exact (boundary _).trans arithmeticValue
      | is_slti_blt_slt =>
        exact (boundary _).trans signedCompareValue
      | is_sltiu_bltu_sltu =>
        exact (boundary _).trans unsignedCompareValue
      | is_lbu_lhu_lw =>
        exact (boundary _).trans unsignedLoadValue
      | is_compare =>
        exact (boundary _).trans compareValue
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

end

end PicoRV.Decoder.InstructionSummary.Structure
