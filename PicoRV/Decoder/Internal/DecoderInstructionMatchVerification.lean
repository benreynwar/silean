import PicoRV.Decoder.DecoderInstructionMatchStructure
import PicoRV.Decoder.DecoderInstructionFieldsTheorems
import PicoRV.Decoder.DecoderInstructionMatchGateTheorems
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction

/-! Internal schedules and structural certification for instruction matching. -/

namespace PicoRV.Decoder.InstructionMatch.Structure

open Silean
open Silean.Authoring
open InstructionFields
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

module_child_certifications childContracts for body where
  fields := InstructionFields.Structure.certification,
  exactMatch (_exact : Exact) := MatchGate.Structure.certification,
  immediateShift01 := Silean.Primitives.orCertified.certification,
  immediateShiftGroup := Silean.Primitives.orCertified.certification,
  arithmetic01 := Silean.Primitives.orCertified.certification,
  arithmetic23 := Silean.Primitives.orCertified.certification,
  arithmetic45 := Silean.Primitives.orCertified.certification,
  arithmetic0123 := Silean.Primitives.orCertified.certification,
  arithmetic012345 := Silean.Primitives.orCertified.certification,
  immediateArithmeticGroup := Silean.Primitives.orCertified.certification,
  registerShift01 := Silean.Primitives.orCertified.certification,
  registerShiftGroup := Silean.Primitives.orCertified.certification

private abbrev occurrence (child : Instance)
    (rule : (childContracts child).RuleName) :
    RuleOccurrence body childContracts := ⟨child, rule⟩

private def fieldOccurrences : List (RuleOccurrence body childContracts) :=
  [occurrence .fields InstructionFields.Rule.apply]

private def exactOccurrences : List (RuleOccurrence body childContracts) :=
  [occurrence (.exactMatch .instr_beq) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_bne) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_blt) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_bge) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_bltu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_bgeu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_lb) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_lh) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_lw) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_lbu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_lhu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sb) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sh) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sw) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_addi) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_slti) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sltiu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_xori) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_ori) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_andi) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_slli) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_srli) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_srai) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_add) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sub) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sll) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_slt) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sltu) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_xor) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_srl) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_sra) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_or) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_and) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_ecall_ebreak) MatchGate.Rule.apply,
   occurrence (.exactMatch .instr_fence) MatchGate.Rule.apply]

private def groupOccurrences : List (RuleOccurrence body childContracts) := [
  occurrence .immediateShift01 Silean.Primitives.OrRule.apply,
  occurrence .immediateShiftGroup Silean.Primitives.OrRule.apply,
  occurrence .arithmetic01 Silean.Primitives.OrRule.apply,
  occurrence .arithmetic23 Silean.Primitives.OrRule.apply,
  occurrence .arithmetic45 Silean.Primitives.OrRule.apply,
  occurrence .arithmetic0123 Silean.Primitives.OrRule.apply,
  occurrence .arithmetic012345 Silean.Primitives.OrRule.apply,
  occurrence .immediateArithmeticGroup Silean.Primitives.OrRule.apply,
  occurrence .registerShift01 Silean.Primitives.OrRule.apply,
  occurrence .registerShiftGroup Silean.Primitives.OrRule.apply]

set_option maxHeartbeats 500000 in
module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => from (fieldOccurrences ++ exactOccurrences ++ groupOccurrences)
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have fieldsValue : hierStep.childOutputs .fields =
      InstructionFields.outputValues (hierStep.inputs .word) := by
    have equation := (InstructionFields.outputRule_holds_iff _ _ _).mp
      ((childMatch .fields).ruleHolds InstructionFields.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have fieldsAt (output : InstructionFields.Output) := congrFun fieldsValue output

  let semanticInputs := valuesOf hierStep.inputs
  have exactValueResult (exact : Exact) :
      hierStep.childOutputs (.exactMatch exact) .result =
        exactValue semanticInputs exact := by
    have equation := (MatchGate.outputRule_holds_iff _ _ _).mp
      ((childMatch (.exactMatch exact)).ruleHolds MatchGate.Rule.apply)
    normalize_child_hyp equation
    simp only [wiring, context] at equation
    have specification := structuralExactValue_eq semanticInputs exact
    cases exact <;>
      simp [semanticInputs, valuesOf, broadValue, fieldValue, exactFunct3,
        qualifierValue, Exact.needsFunct7Zero,
        Exact.needsFunct7Alternate, structuralExactValue,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        fieldsAt, InstructionFields.outputValues]
        at equation specification ⊢ <;>
      exact equation.trans specification

  have immediateShiftValue : hierStep.childOutputs .immediateShiftGroup .output =
      outputValues semanticInputs .is_slli_srli_srai := by
    have shiftPartial := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateShift01).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp shiftPartial unfolding wiring, context
    have shiftPartialResolved := shiftPartial.trans (apply₂_congr Bool.or
      (exactValueResult .instr_slli) (exactValueResult .instr_srli))
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateShiftGroup).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (apply₂_congr Bool.or shiftPartialResolved
      (exactValueResult .instr_srai))).trans ?_
    simp [exactValue, outputValues, matches37, boolOr, List.any]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  have immediateArithmeticValue :
      hierStep.childOutputs .immediateArithmeticGroup .output =
        outputValues semanticInputs .is_jalr_addi_slti_sltiu_xori_ori_andi := by
    have pair01 := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic01).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp pair01 unfolding wiring, context
    have pair01Resolved := pair01.trans (apply₂_congr Bool.or rfl
      (exactValueResult .instr_addi))
    have pair23 := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic23).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp pair23 unfolding wiring, context
    have pair23Resolved := pair23.trans (apply₂_congr Bool.or
      (exactValueResult .instr_slti) (exactValueResult .instr_sltiu))
    have pair45 := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic45).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp pair45 unfolding wiring, context
    have pair45Resolved := pair45.trans (apply₂_congr Bool.or
      (exactValueResult .instr_xori) (exactValueResult .instr_ori))
    have firstFour := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic0123).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp firstFour unfolding wiring, context
    have firstFourResolved := firstFour.trans (apply₂_congr Bool.or
      pair01Resolved pair23Resolved)
    have firstSix := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic012345).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp firstSix unfolding wiring, context
    have firstSixResolved := firstSix.trans (apply₂_congr Bool.or
      firstFourResolved pair45Resolved)
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateArithmeticGroup).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (apply₂_congr Bool.or firstSixResolved
      (exactValueResult .instr_andi))).trans ?_
    simp [exactValue, outputValues, matches3]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]
    simp [semanticInputs, valuesOf]
  have registerShiftValue : hierStep.childOutputs .registerShiftGroup .output =
      outputValues semanticInputs .is_sll_srl_sra := by
    have registerPartial := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .registerShift01).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp registerPartial unfolding wiring, context
    have registerPartialResolved := registerPartial.trans (apply₂_congr Bool.or
      (exactValueResult .instr_sll) (exactValueResult .instr_srl))
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .registerShiftGroup).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (apply₂_congr Bool.or registerPartialResolved
      (exactValueResult .instr_sra))).trans ?_
    simp [exactValue, outputValues, matches37, boolOr, List.any]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]

  have boundary := satisfies.1
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    dsimp only
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output with
    | instr_beq =>
      exact (boundary _).trans (exactValueResult .instr_beq)
    | instr_bne =>
      exact (boundary _).trans (exactValueResult .instr_bne)
    | instr_blt =>
      exact (boundary _).trans (exactValueResult .instr_blt)
    | instr_bge =>
      exact (boundary _).trans (exactValueResult .instr_bge)
    | instr_bltu =>
      exact (boundary _).trans (exactValueResult .instr_bltu)
    | instr_bgeu =>
      exact (boundary _).trans (exactValueResult .instr_bgeu)
    | instr_lb =>
      exact (boundary _).trans (exactValueResult .instr_lb)
    | instr_lh =>
      exact (boundary _).trans (exactValueResult .instr_lh)
    | instr_lw =>
      exact (boundary _).trans (exactValueResult .instr_lw)
    | instr_lbu =>
      exact (boundary _).trans (exactValueResult .instr_lbu)
    | instr_lhu =>
      exact (boundary _).trans (exactValueResult .instr_lhu)
    | instr_sb =>
      exact (boundary _).trans (exactValueResult .instr_sb)
    | instr_sh =>
      exact (boundary _).trans (exactValueResult .instr_sh)
    | instr_sw =>
      exact (boundary _).trans (exactValueResult .instr_sw)
    | instr_addi =>
      exact (boundary _).trans (exactValueResult .instr_addi)
    | instr_slti =>
      exact (boundary _).trans (exactValueResult .instr_slti)
    | instr_sltiu =>
      exact (boundary _).trans (exactValueResult .instr_sltiu)
    | instr_xori =>
      exact (boundary _).trans (exactValueResult .instr_xori)
    | instr_ori =>
      exact (boundary _).trans (exactValueResult .instr_ori)
    | instr_andi =>
      exact (boundary _).trans (exactValueResult .instr_andi)
    | instr_slli =>
      exact (boundary _).trans (exactValueResult .instr_slli)
    | instr_srli =>
      exact (boundary _).trans (exactValueResult .instr_srli)
    | instr_srai =>
      exact (boundary _).trans (exactValueResult .instr_srai)
    | instr_add =>
      exact (boundary _).trans (exactValueResult .instr_add)
    | instr_sub =>
      exact (boundary _).trans (exactValueResult .instr_sub)
    | instr_sll =>
      exact (boundary _).trans (exactValueResult .instr_sll)
    | instr_slt =>
      exact (boundary _).trans (exactValueResult .instr_slt)
    | instr_sltu =>
      exact (boundary _).trans (exactValueResult .instr_sltu)
    | instr_xor =>
      exact (boundary _).trans (exactValueResult .instr_xor)
    | instr_srl =>
      exact (boundary _).trans (exactValueResult .instr_srl)
    | instr_sra =>
      exact (boundary _).trans (exactValueResult .instr_sra)
    | instr_or =>
      exact (boundary _).trans (exactValueResult .instr_or)
    | instr_and =>
      exact (boundary _).trans (exactValueResult .instr_and)
    | instr_ecall_ebreak =>
      exact (boundary _).trans (exactValueResult .instr_ecall_ebreak)
    | instr_fence =>
      exact (boundary _).trans (exactValueResult .instr_fence)
    | is_slli_srli_srai =>
      exact (boundary _).trans immediateShiftValue
    | is_jalr_addi_slti_sltiu_xori_ori_andi =>
      exact (boundary _).trans immediateArithmeticValue
    | is_sll_srl_sra =>
      exact (boundary _).trans registerShiftValue
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

end PicoRV.Decoder.InstructionMatch.Structure
