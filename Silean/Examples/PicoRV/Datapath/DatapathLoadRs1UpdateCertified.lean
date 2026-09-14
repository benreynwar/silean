import Silean.Examples.PicoRV.Datapath.DatapathLoadRs1Update
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified

namespace Silean.Examples.PicoRV.Datapath.LoadRs1Update

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  zeroWord := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  lowFiveRs2 := Modules.VectorLayout.certification 32 5 lowFiveLayout,
  luiOperand := Modules.Mux.certification (.vector 32 .bit),
  selectedOp1 := Modules.Mux.certification (.vector 32 .bit),
  trapOp1 := Modules.Mux.certification (.vector 32 .bit),
  op2Immediate := Modules.Mux.certification (.vector 32 .bit),
  op2Shift := Modules.Mux.certification (.vector 32 .bit),
  op2Load := Modules.Mux.certification (.vector 32 .bit),
  op2Lui := Modules.Mux.certification (.vector 32 .bit),
  trapOp2 := Modules.Mux.certification (.vector 32 .bit),
  shiftImmediate := Modules.Mux.certification (.vector 5 .bit),
  shiftLoad := Modules.Mux.certification (.vector 5 .bit),
  shiftLui := Modules.Mux.certification (.vector 5 .bit),
  trapShift := Modules.Mux.certification (.vector 5 .bit),
  finalShift := Modules.Mux.certification (.vector 5 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    .zeroWord => Primitives.ConstantRule.apply,
    .lowFiveRs2 => Modules.VectorLayout.Rule.apply,
    {.luiOperand, .selectedOp1, .trapOp1, .op2Immediate, .op2Shift,
      .op2Load, .op2Lui, .trapOp2, .shiftImmediate, .shiftLoad,
      .shiftLui, .trapShift, .finalShift} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralOp1 (inputs : Inputs) (current updated : stateMap.Values) : Word :=
  bif inputs.instr_trap then updated .reg_op1
  else bif inputs.is_lui_auipc_jal then
    bif inputs.instr_lui then wordOfNat 0 else current .reg_pc
  else inputs.cpuregs_rs1

def structuralOp2 (inputs : Inputs) (updated : stateMap.Values) : Word :=
  bif inputs.instr_trap then updated .reg_op2
  else bif inputs.is_lui_auipc_jal then inputs.decoded_imm
  else bif inputs.is_lb_lh_lw_lbu_lhu then updated .reg_op2
  else bif inputs.is_slli_srli_srai then updated .reg_op2
  else bif inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then inputs.decoded_imm
  else inputs.cpuregs_rs2

def structuralShift (inputs : Inputs) (updated : stateMap.Values) : FiveBits :=
  bif inputs.instr_trap then updated .reg_sh
  else bif inputs.is_lui_auipc_jal then updated .reg_sh
  else bif inputs.is_lb_lh_lw_lbu_lhu then updated .reg_sh
  else bif inputs.is_slli_srli_srai then inputs.decoded_rs2
  else bif inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then updated .reg_sh
  else lowFiveBits inputs.cpuregs_rs2

def structuralState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .reg_op1 => structuralOp1 inputs current updated
  | .reg_op2 => structuralOp2 inputs updated
  | .reg_sh => structuralShift inputs updated
  | field => updated field

theorem structuralState_eq_loadRs1NextState (inputs : Inputs)
    (current updated : stateMap.Values) :
    structuralState inputs current updated = loadRs1NextState inputs current updated := by
  cases trap : inputs.instr_trap <;> cases lui : inputs.is_lui_auipc_jal <;>
    cases load : inputs.is_lb_lh_lw_lbu_lhu <;>
    cases shift : inputs.is_slli_srli_srai <;>
    cases immediate : inputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
    cases directLui : inputs.instr_lui <;> funext field <;> cases field <;>
    simp [structuralState, structuralOp1, structuralOp2, structuralShift,
      loadRs1NextState, SignalMap.set, trap, lui, load, shift, immediate,
      directLui]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralStateValue proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralStateValue, proposal, satisfies

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have inputField (field : DatapathInputs.Field) :
      (proposal.2 .inputsFields).outputs field = datapathInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have zeroValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).1.1 Primitives.ConstantRule.apply)
  have lowFiveValue : (proposal.2 .lowFiveRs2).outputs .output =
      lowFiveBits datapathInputs.cpuregs_rs2 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 5 lowFiveLayout
      _ _ _ _ (childMatch .lowFiveRs2).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .cpuregs_rs2] at equation
    simp only [Inputs.toValues] at equation
    rw [show Modules.VectorLayout.apply lowFiveLayout datapathInputs.cpuregs_rs2 =
      lowFiveBits datapathInputs.cpuregs_rs2 by rfl] at equation
    exact equation

  have luiOperandValue : (proposal.2 .luiOperand).outputs .result =
      bif datapathInputs.instr_lui then wordOfNat 0 else current .reg_pc := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .luiOperand).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_lui, currentFieldsValue, zeroValue] at equation
    cases instrLui : datapathInputs.instr_lui <;>
      simp [Inputs.toValues, instrLui] at equation ⊢ <;> exact equation
  have selectedOp1Value : (proposal.2 .selectedOp1).outputs .result =
      bif datapathInputs.is_lui_auipc_jal then
        (bif datapathInputs.instr_lui then wordOfNat 0 else current .reg_pc)
      else datapathInputs.cpuregs_rs1 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_lui_auipc_jal, inputField .cpuregs_rs1,
      luiOperandValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have op1Value : (proposal.2 .trapOp1).outputs .result =
      structuralOp1 datapathInputs current updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .trapOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_trap, selectedOp1Value, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralOp1, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have op2ImmediateValue : (proposal.2 .op2Immediate).outputs .result =
      bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .op2Immediate).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_jalr_addi_slti_sltiu_xori_ori_andi,
      inputField .decoded_imm, inputField .cpuregs_rs2] at equation
    cases immediate : datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      simp [Inputs.toValues, immediate] at equation ⊢ <;> exact equation
  have op2ShiftValue : (proposal.2 .op2Shift).outputs .result =
      bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .op2Shift).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_slli_srli_srai, op2ImmediateValue,
      updatedFieldsValue] at equation
    cases shift : datapathInputs.is_slli_srli_srai <;>
      simp [Inputs.toValues, shift] at equation ⊢ <;> exact equation
  have op2LoadValue : (proposal.2 .op2Load).outputs .result =
      bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_op2
      else (bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2)) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .op2Load).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_lb_lh_lw_lbu_lhu, op2ShiftValue,
      updatedFieldsValue] at equation
    cases load : datapathInputs.is_lb_lh_lw_lbu_lhu <;>
      simp [Inputs.toValues, load] at equation ⊢ <;> exact equation
  have op2LuiValue : (proposal.2 .op2Lui).outputs .result =
      bif datapathInputs.is_lui_auipc_jal then datapathInputs.decoded_imm
      else (bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_op2
      else (bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2))) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .op2Lui).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_lui_auipc_jal, inputField .decoded_imm,
      op2LoadValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have op2Value : (proposal.2 .trapOp2).outputs .result =
      structuralOp2 datapathInputs updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .trapOp2).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_trap, op2LuiValue, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralOp2, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have shiftImmediateValue : (proposal.2 .shiftImmediate).outputs .result =
      bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .shiftImmediate).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_jalr_addi_slti_sltiu_xori_ori_andi,
      lowFiveValue, updatedFieldsValue] at equation
    cases immediate : datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      simp [Inputs.toValues, immediate] at equation ⊢ <;> exact equation
  have shiftLoadValue : (proposal.2 .shiftLoad).outputs .result =
      bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .shiftLoad).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_slli_srli_srai, inputField .decoded_rs2,
      shiftImmediateValue] at equation
    cases shift : datapathInputs.is_slli_srli_srai <;>
      simp [Inputs.toValues, shift] at equation ⊢ <;> exact equation
  have shiftLuiValue : (proposal.2 .shiftLui).outputs .result =
      bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_sh
      else (bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2)) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .shiftLui).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_lb_lh_lw_lbu_lhu, shiftLoadValue,
      updatedFieldsValue] at equation
    cases load : datapathInputs.is_lb_lh_lw_lbu_lhu <;>
      simp [Inputs.toValues, load] at equation ⊢ <;> exact equation
  have trapShiftValue : (proposal.2 .trapShift).outputs .result =
      bif datapathInputs.is_lui_auipc_jal then updated .reg_sh
      else (bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_sh
      else (bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2))) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .trapShift).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_lui_auipc_jal, shiftLuiValue,
      updatedFieldsValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have shiftValue : (proposal.2 .finalShift).outputs .result =
      structuralShift datapathInputs updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .finalShift).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_trap, trapShiftValue, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralShift, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralState datapathInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState]
    · simpa using congrFun updatedFieldsValue .reg_pc
    · simpa using congrFun updatedFieldsValue .reg_next_pc
    · exact op1Value
    · exact op2Value
    · simpa using congrFun updatedFieldsValue .reg_out
    · exact shiftValue
    · simpa using congrFun updatedFieldsValue .alu_out_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (loadRs1NextState datapathInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_loadRs1NextState] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
      exact satisfies.1 .state]
    simpa [StateUpdate.outputState, datapathInputs, current, updated] using resultValue
  · rfl

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

end Silean.Examples.PicoRV.Datapath.LoadRs1Update
