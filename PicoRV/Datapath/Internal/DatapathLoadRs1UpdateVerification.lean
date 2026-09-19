import PicoRV.Datapath.DatapathLoadRs1Update
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems

namespace PicoRV.Datapath.LoadRs1Update

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  zeroWord := Silean.Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  lowFiveRs2 := Silean.Modules.VectorLayout.certification 32 5 lowFiveLayout,
  luiOperand := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectedOp1 := Silean.Modules.Mux.certification (.vector 32 .bit),
  trapOp1 := Silean.Modules.Mux.certification (.vector 32 .bit),
  op2Immediate := Silean.Modules.Mux.certification (.vector 32 .bit),
  op2Shift := Silean.Modules.Mux.certification (.vector 32 .bit),
  op2Load := Silean.Modules.Mux.certification (.vector 32 .bit),
  op2Lui := Silean.Modules.Mux.certification (.vector 32 .bit),
  trapOp2 := Silean.Modules.Mux.certification (.vector 32 .bit),
  shiftImmediate := Silean.Modules.Mux.certification (.vector 5 .bit),
  shiftLoad := Silean.Modules.Mux.certification (.vector 5 .bit),
  shiftLui := Silean.Modules.Mux.certification (.vector 5 .bit),
  trapShift := Silean.Modules.Mux.certification (.vector 5 .bit),
  finalShift := Silean.Modules.Mux.certification (.vector 5 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    .zeroWord => Silean.Primitives.ConstantRule.apply,
    .lowFiveRs2 => Silean.Modules.VectorLayout.Rule.apply,
    {.luiOperand, .selectedOp1, .trapOp1, .op2Immediate, .op2Shift,
      .op2Load, .op2Lui, .trapOp2, .shiftImmediate, .shiftLoad,
      .shiftLui, .trapShift, .finalShift} => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
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
      loadRs1NextState, Silean.SignalMap.set, trap, lui, load, shift, immediate,
      directLui]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have inputField (field : DatapathInputs.Field) :
      hierStep.childOutputs .inputsFields field = datapathInputs.toValues field := by
    exact (congrFun inputsFieldsValue field).trans
      (congrFun (Inputs.toValues_unpack _).symm field)
  have zeroValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).ruleHolds Silean.Primitives.ConstantRule.apply)
  have lowFiveValue : hierStep.childOutputs .lowFiveRs2 .output =
      lowFiveBits datapathInputs.cpuregs_rs2 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 5 lowFiveLayout
      (childMatch .lowFiveRs2).allowed
    change hierStep.childOutputs .lowFiveRs2 .output =
      Silean.Modules.VectorLayout.apply lowFiveLayout
        (hierStep.childOutputs .inputsFields .cpuregs_rs2) at equation
    rw [inputField .cpuregs_rs2] at equation
    simp only [Inputs.toValues] at equation
    rw [show Silean.Modules.VectorLayout.apply lowFiveLayout datapathInputs.cpuregs_rs2 =
      lowFiveBits datapathInputs.cpuregs_rs2 by rfl] at equation
    exact equation

  have luiOperandValue : hierStep.childOutputs .luiOperand .result =
      bif datapathInputs.instr_lui then wordOfNat 0 else current .reg_pc := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .luiOperand).allowed
    change hierStep.childOutputs .luiOperand .result = bif
      hierStep.childOutputs .inputsFields .instr_lui
      then hierStep.childOutputs .zeroWord .output
      else hierStep.childOutputs .currentFields .reg_pc at equation
    rw [inputField .instr_lui, currentFieldsValue, zeroValue] at equation
    cases instrLui : datapathInputs.instr_lui <;>
      simp [Inputs.toValues, instrLui] at equation ⊢ <;> exact equation
  have selectedOp1Value : hierStep.childOutputs .selectedOp1 .result =
      bif datapathInputs.is_lui_auipc_jal then
        (bif datapathInputs.instr_lui then wordOfNat 0 else current .reg_pc)
      else datapathInputs.cpuregs_rs1 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedOp1).allowed
    change hierStep.childOutputs .selectedOp1 .result = bif
      hierStep.childOutputs .inputsFields .is_lui_auipc_jal
      then hierStep.childOutputs .luiOperand .result
      else hierStep.childOutputs .inputsFields .cpuregs_rs1 at equation
    rw [inputField .is_lui_auipc_jal, inputField .cpuregs_rs1,
      luiOperandValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have op1Value : hierStep.childOutputs .trapOp1 .result =
      structuralOp1 datapathInputs current updated := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .trapOp1).allowed
    change hierStep.childOutputs .trapOp1 .result = bif
      hierStep.childOutputs .inputsFields .instr_trap
      then hierStep.childOutputs .updatedFields .reg_op1
      else hierStep.childOutputs .selectedOp1 .result at equation
    rw [inputField .instr_trap, selectedOp1Value, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralOp1, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have op2ImmediateValue : hierStep.childOutputs .op2Immediate .result =
      bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .op2Immediate).allowed
    change hierStep.childOutputs .op2Immediate .result = bif
      hierStep.childOutputs .inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi
      then hierStep.childOutputs .inputsFields .decoded_imm
      else hierStep.childOutputs .inputsFields .cpuregs_rs2 at equation
    rw [inputField .is_jalr_addi_slti_sltiu_xori_ori_andi,
      inputField .decoded_imm, inputField .cpuregs_rs2] at equation
    cases immediate : datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      simp [Inputs.toValues, immediate] at equation ⊢ <;> exact equation
  have op2ShiftValue : hierStep.childOutputs .op2Shift .result =
      bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .op2Shift).allowed
    change hierStep.childOutputs .op2Shift .result = bif
      hierStep.childOutputs .inputsFields .is_slli_srli_srai
      then hierStep.childOutputs .updatedFields .reg_op2
      else hierStep.childOutputs .op2Immediate .result at equation
    rw [inputField .is_slli_srli_srai, op2ImmediateValue,
      updatedFieldsValue] at equation
    cases shift : datapathInputs.is_slli_srli_srai <;>
      simp [Inputs.toValues, shift] at equation ⊢ <;> exact equation
  have op2LoadValue : hierStep.childOutputs .op2Load .result =
      bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_op2
      else (bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2)) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .op2Load).allowed
    change hierStep.childOutputs .op2Load .result = bif
      hierStep.childOutputs .inputsFields .is_lb_lh_lw_lbu_lhu
      then hierStep.childOutputs .updatedFields .reg_op2
      else hierStep.childOutputs .op2Shift .result at equation
    rw [inputField .is_lb_lh_lw_lbu_lhu, op2ShiftValue,
      updatedFieldsValue] at equation
    cases load : datapathInputs.is_lb_lh_lw_lbu_lhu <;>
      simp [Inputs.toValues, load] at equation ⊢ <;> exact equation
  have op2LuiValue : hierStep.childOutputs .op2Lui .result =
      bif datapathInputs.is_lui_auipc_jal then datapathInputs.decoded_imm
      else (bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_op2
      else (bif datapathInputs.is_slli_srli_srai then updated .reg_op2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        datapathInputs.decoded_imm else datapathInputs.cpuregs_rs2))) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .op2Lui).allowed
    change hierStep.childOutputs .op2Lui .result = bif
      hierStep.childOutputs .inputsFields .is_lui_auipc_jal
      then hierStep.childOutputs .inputsFields .decoded_imm
      else hierStep.childOutputs .op2Load .result at equation
    rw [inputField .is_lui_auipc_jal, inputField .decoded_imm,
      op2LoadValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have op2Value : hierStep.childOutputs .trapOp2 .result =
      structuralOp2 datapathInputs updated := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .trapOp2).allowed
    change hierStep.childOutputs .trapOp2 .result = bif
      hierStep.childOutputs .inputsFields .instr_trap
      then hierStep.childOutputs .updatedFields .reg_op2
      else hierStep.childOutputs .op2Lui .result at equation
    rw [inputField .instr_trap, op2LuiValue, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralOp2, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have shiftImmediateValue : hierStep.childOutputs .shiftImmediate .result =
      bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .shiftImmediate).allowed
    change hierStep.childOutputs .shiftImmediate .result = bif
      hierStep.childOutputs .inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi
      then hierStep.childOutputs .updatedFields .reg_sh
      else hierStep.childOutputs .lowFiveRs2 .output at equation
    rw [inputField .is_jalr_addi_slti_sltiu_xori_ori_andi,
      lowFiveValue, updatedFieldsValue] at equation
    cases immediate : datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      simp [Inputs.toValues, immediate] at equation ⊢ <;> exact equation
  have shiftLoadValue : hierStep.childOutputs .shiftLoad .result =
      bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .shiftLoad).allowed
    change hierStep.childOutputs .shiftLoad .result = bif
      hierStep.childOutputs .inputsFields .is_slli_srli_srai
      then hierStep.childOutputs .inputsFields .decoded_rs2
      else hierStep.childOutputs .shiftImmediate .result at equation
    rw [inputField .is_slli_srli_srai, inputField .decoded_rs2,
      shiftImmediateValue] at equation
    cases shift : datapathInputs.is_slli_srli_srai <;>
      simp [Inputs.toValues, shift] at equation ⊢ <;> exact equation
  have shiftLuiValue : hierStep.childOutputs .shiftLui .result =
      bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_sh
      else (bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2)) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .shiftLui).allowed
    change hierStep.childOutputs .shiftLui .result = bif
      hierStep.childOutputs .inputsFields .is_lb_lh_lw_lbu_lhu
      then hierStep.childOutputs .updatedFields .reg_sh
      else hierStep.childOutputs .shiftLoad .result at equation
    rw [inputField .is_lb_lh_lw_lbu_lhu, shiftLoadValue,
      updatedFieldsValue] at equation
    cases load : datapathInputs.is_lb_lh_lw_lbu_lhu <;>
      simp [Inputs.toValues, load] at equation ⊢ <;> exact equation
  have trapShiftValue : hierStep.childOutputs .trapShift .result =
      bif datapathInputs.is_lui_auipc_jal then updated .reg_sh
      else (bif datapathInputs.is_lb_lh_lw_lbu_lhu then updated .reg_sh
      else (bif datapathInputs.is_slli_srli_srai then datapathInputs.decoded_rs2
      else (bif datapathInputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
        updated .reg_sh else lowFiveBits datapathInputs.cpuregs_rs2))) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .trapShift).allowed
    change hierStep.childOutputs .trapShift .result = bif
      hierStep.childOutputs .inputsFields .is_lui_auipc_jal
      then hierStep.childOutputs .updatedFields .reg_sh
      else hierStep.childOutputs .shiftLui .result at equation
    rw [inputField .is_lui_auipc_jal, shiftLuiValue,
      updatedFieldsValue] at equation
    cases lui : datapathInputs.is_lui_auipc_jal <;>
      simp [Inputs.toValues, lui] at equation ⊢ <;> exact equation
  have shiftValue : hierStep.childOutputs .finalShift .result =
      structuralShift datapathInputs updated := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .finalShift).allowed
    change hierStep.childOutputs .finalShift .result = bif
      hierStep.childOutputs .inputsFields .instr_trap
      then hierStep.childOutputs .updatedFields .reg_sh
      else hierStep.childOutputs .trapShift .result at equation
    rw [inputField .instr_trap, trapShiftValue, updatedFieldsValue] at equation
    cases trap : datapathInputs.instr_trap <;>
      simp [structuralShift, Inputs.toValues, trap] at equation ⊢ <;>
      exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralState datapathInputs current updated := by
    funext field
    cases field
    · change hierStep.childOutputs .updatedFields .reg_pc = _
      exact congrFun updatedFieldsValue .reg_pc
    · change hierStep.childOutputs .updatedFields .reg_next_pc = _
      exact congrFun updatedFieldsValue .reg_next_pc
    · change hierStep.childOutputs .trapOp1 .result = _; exact op1Value
    · change hierStep.childOutputs .trapOp2 .result = _; exact op2Value
    · change hierStep.childOutputs .updatedFields .reg_out = _
      exact congrFun updatedFieldsValue .reg_out
    · change hierStep.childOutputs .finalShift .result = _; exact shiftValue
    · change hierStep.childOutputs .updatedFields .alu_out_q = _
      exact congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (loadRs1NextState datapathInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_loadRs1NextState] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.LoadRs1Update
