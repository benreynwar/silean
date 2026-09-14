import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchStructure
import Silean.Examples.PicoRV.Decoder.DecoderInstructionFieldsCertified
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchGateCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch.Structure

open Silean
open Silean.Authoring
open InstructionFields
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

module_child_certifications childContracts for body where
  fields := InstructionFields.Structure.certification,
  exactMatch (_exact : Exact) := MatchGate.Structure.certification,
  immediateShift01 := Primitives.orCertified.certification,
  immediateShiftGroup := Primitives.orCertified.certification,
  arithmetic01 := Primitives.orCertified.certification,
  arithmetic23 := Primitives.orCertified.certification,
  arithmetic45 := Primitives.orCertified.certification,
  arithmetic0123 := Primitives.orCertified.certification,
  arithmetic012345 := Primitives.orCertified.certification,
  immediateArithmeticGroup := Primitives.orCertified.certification,
  registerShift01 := Primitives.orCertified.certification,
  registerShiftGroup := Primitives.orCertified.certification

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
  occurrence .immediateShift01 Primitives.OrRule.apply,
  occurrence .immediateShiftGroup Primitives.OrRule.apply,
  occurrence .arithmetic01 Primitives.OrRule.apply,
  occurrence .arithmetic23 Primitives.OrRule.apply,
  occurrence .arithmetic45 Primitives.OrRule.apply,
  occurrence .arithmetic0123 Primitives.OrRule.apply,
  occurrence .arithmetic012345 Primitives.OrRule.apply,
  occurrence .immediateArithmeticGroup Primitives.OrRule.apply,
  occurrence .registerShift01 Primitives.OrRule.apply,
  occurrence .registerShiftGroup Primitives.OrRule.apply]

set_option maxHeartbeats 500000 in
module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => from (fieldOccurrences ++ exactOccurrences ++ groupOccurrences)
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  have fieldsValue : (proposal.2 .fields).outputs =
      InstructionFields.outputValues (inputs .word) := by
    have equation := (InstructionFields.outputRule_holds_iff _ _ _).mp
      ((childMatch .fields).1.1 InstructionFields.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have funct7ZeroValue : (proposal.2 .fields).outputs .funct7_zero =
      decide (funct7 (inputs .word) = 0) := congrFun fieldsValue .funct7_zero
  have funct7AlternateValue : (proposal.2 .fields).outputs .funct7_alternate =
      decide (funct7 (inputs .word) = 0x20) :=
    congrFun fieldsValue .funct7_alternate
  have trueValue : (proposal.2 .fields).outputs .true_value = true :=
    congrFun fieldsValue .true_value

  let semanticInputs := valuesOf inputs
  have exactValueResult (exact : Exact) :
      (proposal.2 (.exactMatch exact)).outputs .result =
        exactValue semanticInputs exact := by
    have equation := (MatchGate.outputRule_holds_iff _ _ _).mp
      ((childMatch (.exactMatch exact)).1.1 MatchGate.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    have specification := structuralExactValue_eq semanticInputs exact
    cases exact <;>
      simp [fieldsValue, InstructionFields.outputValues] at equation <;>
      simp [semanticInputs, valuesOf, broadValue, fieldValue, exactFunct3,
        qualifierValue, Exact.needsFunct7Zero,
        Exact.needsFunct7Alternate, structuralExactValue,
        funct7ZeroValue, funct7AlternateValue, trueValue]
        at equation specification ⊢ <;>
      exact equation.trans specification

  have immediateShiftValue : (proposal.2 .immediateShiftGroup).outputs .output =
      outputValues semanticInputs .is_slli_srli_srai := by
    have shiftPartial := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateShift01).1.1 Primitives.OrRule.apply)
    normalize_child_hyp shiftPartial unfolding body, wiring, context
    rw [exactValueResult .instr_slli, exactValueResult .instr_srli] at shiftPartial
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateShiftGroup).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftPartial, exactValueResult .instr_srai] at equation
    rw [equation]
    simp [exactValue, outputValues, matches37, boolOr, List.any]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  have immediateArithmeticValue :
      (proposal.2 .immediateArithmeticGroup).outputs .output =
        outputValues semanticInputs .is_jalr_addi_slti_sltiu_xori_ori_andi := by
    have pair01 := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic01).1.1 Primitives.OrRule.apply)
    normalize_child_hyp pair01 unfolding body, wiring, context
    rw [exactValueResult .instr_addi] at pair01
    have pair23 := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic23).1.1 Primitives.OrRule.apply)
    normalize_child_hyp pair23 unfolding body, wiring, context
    rw [exactValueResult .instr_slti, exactValueResult .instr_sltiu] at pair23
    have pair45 := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic45).1.1 Primitives.OrRule.apply)
    normalize_child_hyp pair45 unfolding body, wiring, context
    rw [exactValueResult .instr_xori, exactValueResult .instr_ori] at pair45
    have firstFour := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic0123).1.1 Primitives.OrRule.apply)
    normalize_child_hyp firstFour unfolding body, wiring, context
    rw [pair01, pair23] at firstFour
    have firstSix := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmetic012345).1.1 Primitives.OrRule.apply)
    normalize_child_hyp firstSix unfolding body, wiring, context
    rw [firstFour, pair45] at firstSix
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .immediateArithmeticGroup).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [firstSix, exactValueResult .instr_andi] at equation
    rw [equation]
    simp [exactValue, outputValues, matches3]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]
    simp [semanticInputs, valuesOf]
  have registerShiftValue : (proposal.2 .registerShiftGroup).outputs .output =
      outputValues semanticInputs .is_sll_srl_sra := by
    have registerPartial := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .registerShift01).1.1 Primitives.OrRule.apply)
    normalize_child_hyp registerPartial unfolding body, wiring, context
    rw [exactValueResult .instr_sll, exactValueResult .instr_srl] at registerPartial
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .registerShiftGroup).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [registerPartial, exactValueResult .instr_sra] at equation
    rw [equation]
    simp [exactValue, outputValues, matches37, boolOr, List.any]
    simp only [Bool.and_or_distrib_left, Bool.or_assoc]

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output with
    | instr_beq =>
      rw [show proposal.outputs .instr_beq =
        (proposal.2 (.exactMatch .instr_beq)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_beq]
      rfl
    | instr_bne =>
      rw [show proposal.outputs .instr_bne =
        (proposal.2 (.exactMatch .instr_bne)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_bne]
      rfl
    | instr_blt =>
      rw [show proposal.outputs .instr_blt =
        (proposal.2 (.exactMatch .instr_blt)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_blt]
      rfl
    | instr_bge =>
      rw [show proposal.outputs .instr_bge =
        (proposal.2 (.exactMatch .instr_bge)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_bge]
      rfl
    | instr_bltu =>
      rw [show proposal.outputs .instr_bltu =
        (proposal.2 (.exactMatch .instr_bltu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_bltu]
      rfl
    | instr_bgeu =>
      rw [show proposal.outputs .instr_bgeu =
        (proposal.2 (.exactMatch .instr_bgeu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_bgeu]
      rfl
    | instr_lb =>
      rw [show proposal.outputs .instr_lb =
        (proposal.2 (.exactMatch .instr_lb)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_lb]
      rfl
    | instr_lh =>
      rw [show proposal.outputs .instr_lh =
        (proposal.2 (.exactMatch .instr_lh)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_lh]
      rfl
    | instr_lw =>
      rw [show proposal.outputs .instr_lw =
        (proposal.2 (.exactMatch .instr_lw)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_lw]
      rfl
    | instr_lbu =>
      rw [show proposal.outputs .instr_lbu =
        (proposal.2 (.exactMatch .instr_lbu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_lbu]
      rfl
    | instr_lhu =>
      rw [show proposal.outputs .instr_lhu =
        (proposal.2 (.exactMatch .instr_lhu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_lhu]
      rfl
    | instr_sb =>
      rw [show proposal.outputs .instr_sb =
        (proposal.2 (.exactMatch .instr_sb)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sb]
      rfl
    | instr_sh =>
      rw [show proposal.outputs .instr_sh =
        (proposal.2 (.exactMatch .instr_sh)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sh]
      rfl
    | instr_sw =>
      rw [show proposal.outputs .instr_sw =
        (proposal.2 (.exactMatch .instr_sw)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sw]
      rfl
    | instr_addi =>
      rw [show proposal.outputs .instr_addi =
        (proposal.2 (.exactMatch .instr_addi)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_addi]
      rfl
    | instr_slti =>
      rw [show proposal.outputs .instr_slti =
        (proposal.2 (.exactMatch .instr_slti)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_slti]
      rfl
    | instr_sltiu =>
      rw [show proposal.outputs .instr_sltiu =
        (proposal.2 (.exactMatch .instr_sltiu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sltiu]
      rfl
    | instr_xori =>
      rw [show proposal.outputs .instr_xori =
        (proposal.2 (.exactMatch .instr_xori)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_xori]
      rfl
    | instr_ori =>
      rw [show proposal.outputs .instr_ori =
        (proposal.2 (.exactMatch .instr_ori)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_ori]
      rfl
    | instr_andi =>
      rw [show proposal.outputs .instr_andi =
        (proposal.2 (.exactMatch .instr_andi)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_andi]
      rfl
    | instr_slli =>
      rw [show proposal.outputs .instr_slli =
        (proposal.2 (.exactMatch .instr_slli)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_slli]
      rfl
    | instr_srli =>
      rw [show proposal.outputs .instr_srli =
        (proposal.2 (.exactMatch .instr_srli)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_srli]
      rfl
    | instr_srai =>
      rw [show proposal.outputs .instr_srai =
        (proposal.2 (.exactMatch .instr_srai)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_srai]
      rfl
    | instr_add =>
      rw [show proposal.outputs .instr_add =
        (proposal.2 (.exactMatch .instr_add)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_add]
      rfl
    | instr_sub =>
      rw [show proposal.outputs .instr_sub =
        (proposal.2 (.exactMatch .instr_sub)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sub]
      rfl
    | instr_sll =>
      rw [show proposal.outputs .instr_sll =
        (proposal.2 (.exactMatch .instr_sll)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sll]
      rfl
    | instr_slt =>
      rw [show proposal.outputs .instr_slt =
        (proposal.2 (.exactMatch .instr_slt)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_slt]
      rfl
    | instr_sltu =>
      rw [show proposal.outputs .instr_sltu =
        (proposal.2 (.exactMatch .instr_sltu)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sltu]
      rfl
    | instr_xor =>
      rw [show proposal.outputs .instr_xor =
        (proposal.2 (.exactMatch .instr_xor)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_xor]
      rfl
    | instr_srl =>
      rw [show proposal.outputs .instr_srl =
        (proposal.2 (.exactMatch .instr_srl)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_srl]
      rfl
    | instr_sra =>
      rw [show proposal.outputs .instr_sra =
        (proposal.2 (.exactMatch .instr_sra)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_sra]
      rfl
    | instr_or =>
      rw [show proposal.outputs .instr_or =
        (proposal.2 (.exactMatch .instr_or)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_or]
      rfl
    | instr_and =>
      rw [show proposal.outputs .instr_and =
        (proposal.2 (.exactMatch .instr_and)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_and]
      rfl
    | instr_ecall_ebreak =>
      rw [show proposal.outputs .instr_ecall_ebreak =
        (proposal.2 (.exactMatch .instr_ecall_ebreak)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_ecall_ebreak]
      rfl
    | instr_fence =>
      rw [show proposal.outputs .instr_fence =
        (proposal.2 (.exactMatch .instr_fence)).outputs .result by exact boundary _]
      rw [exactValueResult .instr_fence]
      rfl
    | is_slli_srli_srai =>
      rw [show proposal.outputs .is_slli_srli_srai =
        (proposal.2 .immediateShiftGroup).outputs .output by exact boundary _]
      rw [immediateShiftValue]
    | is_jalr_addi_slti_sltiu_xori_ori_andi =>
      rw [show proposal.outputs .is_jalr_addi_slti_sltiu_xori_ori_andi =
        (proposal.2 .immediateArithmeticGroup).outputs .output by exact boundary _]
      rw [immediateArithmeticValue]
    | is_sll_srl_sra =>
      rw [show proposal.outputs .is_sll_srl_sra =
        (proposal.2 .registerShiftGroup).outputs .output by exact boundary _]
      rw [registerShiftValue]
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

end Silean.Examples.PicoRV.Decoder.InstructionMatch.Structure
