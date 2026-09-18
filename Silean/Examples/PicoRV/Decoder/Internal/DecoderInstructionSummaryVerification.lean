import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummaryStructure
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Any.Any
import Silean.Primitives.Not

/-! Internal schedules and structural certification for instruction summaries. -/

namespace Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

noncomputable section

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

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have recognizedValue := (Modules.Any.outputRule_holds_iff_width 38 _ _ _).mp
      ((childMatch .recognized).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp recognizedValue unfolding wiring, context
  change hierStep.childOutputs .recognized .output =
    recognized (valuesOf hierStep.inputs) at recognizedValue
  have trapValue : hierStep.childOutputs .trap .output =
      outputValues (valuesOf hierStep.inputs) .instr_trap := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .trap).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact (equation.trans (congrArg Bool.not recognizedValue)).trans <| by
      rfl

  have luiAuipcJalValue := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .luiAuipcJal).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp luiAuipcJalValue unfolding wiring, context
  change hierStep.childOutputs .luiAuipcJal .output =
    outputValues (valuesOf hierStep.inputs) .is_lui_auipc_jal at luiAuipcJalValue
  have arithmeticValue := (Modules.Any.outputRule_holds_iff_width 7 _ _ _).mp
      ((childMatch .arithmetic).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp arithmeticValue unfolding wiring, context
  change hierStep.childOutputs .arithmetic .output =
    outputValues (valuesOf hierStep.inputs) .is_lui_auipc_jal_jalr_addi_add_sub
    at arithmeticValue
  have signedCompareValue := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .signedCompare).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp signedCompareValue unfolding wiring, context
  change hierStep.childOutputs .signedCompare .output =
    outputValues (valuesOf hierStep.inputs) .is_slti_blt_slt at signedCompareValue
  have unsignedCompareValue := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedCompare).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp unsignedCompareValue unfolding wiring, context
  change hierStep.childOutputs .unsignedCompare .output =
    outputValues (valuesOf hierStep.inputs) .is_sltiu_bltu_sltu at unsignedCompareValue
  have unsignedLoadValue := (Modules.Any.outputRule_holds_iff_width 3 _ _ _).mp
      ((childMatch .unsignedLoad).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp unsignedLoadValue unfolding wiring, context
  change hierStep.childOutputs .unsignedLoad .output =
    outputValues (valuesOf hierStep.inputs) .is_lbu_lhu_lw at unsignedLoadValue
  have compareValue := (Modules.Any.outputRule_holds_iff_width 5 _ _ _).mp
      ((childMatch .compare).ruleHolds Modules.Any.Rule.apply)
  normalize_child_hyp compareValue unfolding wiring, context
  change hierStep.childOutputs .compare .output =
    outputValues (valuesOf hierStep.inputs) .is_compare at compareValue

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end

end Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure
