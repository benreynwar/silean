import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! The second registered decoder stage. It resolves broad capture-stage
classes into exact instructions, constructs the non-J immediate, and maintains
the registered summary flags with the source's pre-edge timing and priorities. -/

module_ports ports where
  input resetn : .bit,
  input decoder_trigger : .bit,
  input decoder_pseudo_trigger : .bit,
  input mem_rdata_q : .vector 32 .bit,
  input instr_lui : .bit,
  input instr_auipc : .bit,
  input instr_jal : .bit,
  input instr_jalr : .bit,
  input decoded_imm_j : .vector 32 .bit,
  input is_beq_bne_blt_bge_bltu_bgeu : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_sb_sh_sw : .bit,
  input is_alu_reg_imm : .bit,
  input is_alu_reg_reg : .bit,
  output instr_trap : .bit,
  output instr_beq : .bit,
  output instr_bne : .bit,
  output instr_blt : .bit,
  output instr_bge : .bit,
  output instr_bltu : .bit,
  output instr_bgeu : .bit,
  output instr_lb : .bit,
  output instr_lh : .bit,
  output instr_lw : .bit,
  output instr_lbu : .bit,
  output instr_lhu : .bit,
  output instr_sb : .bit,
  output instr_sh : .bit,
  output instr_sw : .bit,
  output instr_addi : .bit,
  output instr_slti : .bit,
  output instr_sltiu : .bit,
  output instr_xori : .bit,
  output instr_ori : .bit,
  output instr_andi : .bit,
  output instr_slli : .bit,
  output instr_srli : .bit,
  output instr_srai : .bit,
  output instr_add : .bit,
  output instr_sub : .bit,
  output instr_sll : .bit,
  output instr_slt : .bit,
  output instr_sltu : .bit,
  output instr_xor : .bit,
  output instr_srl : .bit,
  output instr_sra : .bit,
  output instr_or : .bit,
  output instr_and : .bit,
  output instr_fence : .bit,
  output decoded_imm : .vector 32 .bit,
  output is_lui_auipc_jal : .bit,
  output is_slli_srli_srai : .bit,
  output is_jalr_addi_slti_sltiu_xori_ori_andi : .bit,
  output is_sll_srl_sra : .bit,
  output is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  output is_slti_blt_slt : .bit,
  output is_sltiu_bltu_sltu : .bit,
  output is_lbu_lhu_lw : .bit,
  output is_compare : .bit

inductive Register
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
  | decoded_imm
  | is_lui_auipc_jal
  | is_slli_srli_srai
  | is_jalr_addi_slti_sltiu_xori_ori_andi
  | is_sll_srl_sra
  | is_lui_auipc_jal_jalr_addi_add_sub
  | is_slti_blt_slt
  | is_sltiu_bltu_sltu
  | is_lbu_lhu_lw
  | is_compare
deriving Enumeration

def registerType : Register → SignalType
  | .decoded_imm => .vector 32 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of Register registerType

structure Inputs where
  resetn : Bool
  decoder_trigger : Bool
  decoder_pseudo_trigger : Bool
  mem_rdata_q : Word
  instr_lui : Bool
  instr_auipc : Bool
  instr_jal : Bool
  instr_jalr : Bool
  decoded_imm_j : Word
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_sb_sh_sw : Bool
  is_alu_reg_imm : Bool
  is_alu_reg_reg : Bool

def valuesOf (inputs : inputMap.Values) : Inputs where
  resetn := inputs .resetn
  decoder_trigger := inputs .decoder_trigger
  decoder_pseudo_trigger := inputs .decoder_pseudo_trigger
  mem_rdata_q := inputs .mem_rdata_q
  instr_lui := inputs .instr_lui
  instr_auipc := inputs .instr_auipc
  instr_jal := inputs .instr_jal
  instr_jalr := inputs .instr_jalr
  decoded_imm_j := inputs .decoded_imm_j
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  is_lb_lh_lw_lbu_lhu := inputs .is_lb_lh_lw_lbu_lhu
  is_sb_sh_sw := inputs .is_sb_sh_sw
  is_alu_reg_imm := inputs .is_alu_reg_imm
  is_alu_reg_reg := inputs .is_alu_reg_reg

def summarized (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let state := stateMap.set state .is_lui_auipc_jal
    (boolOr [inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal])
  let state := stateMap.set state .is_lui_auipc_jal_jalr_addi_add_sub
    (boolOr [inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal,
      inputs.instr_jalr, state .instr_addi, state .instr_add, state .instr_sub])
  let state := stateMap.set state .is_slti_blt_slt
    (boolOr [state .instr_slti, state .instr_blt, state .instr_slt])
  let state := stateMap.set state .is_sltiu_bltu_sltu
    (boolOr [state .instr_sltiu, state .instr_bltu, state .instr_sltu])
  let state := stateMap.set state .is_lbu_lhu_lw
    (boolOr [state .instr_lbu, state .instr_lhu, state .instr_lw])
  stateMap.set state .is_compare
    (boolOr [inputs.is_beq_bne_blt_bge_bltu_bgeu,
      state .instr_slti, state .instr_slt, state .instr_sltiu, state .instr_sltu])

def decoded (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  if !(inputs.decoder_trigger && !inputs.decoder_pseudo_trigger) then updated else
  let word := inputs.mem_rdata_q
  let branch := inputs.is_beq_bne_blt_bge_bltu_bgeu
  let load := inputs.is_lb_lh_lw_lbu_lhu
  let store := inputs.is_sb_sh_sw
  let imm := inputs.is_alu_reg_imm
  let reg := inputs.is_alu_reg_reg
  let state := updated
  let state := stateMap.set state .instr_beq (branch && decide (funct3 word = 0))
  let state := stateMap.set state .instr_bne (branch && decide (funct3 word = 1))
  let state := stateMap.set state .instr_blt (branch && decide (funct3 word = 4))
  let state := stateMap.set state .instr_bge (branch && decide (funct3 word = 5))
  let state := stateMap.set state .instr_bltu (branch && decide (funct3 word = 6))
  let state := stateMap.set state .instr_bgeu (branch && decide (funct3 word = 7))
  let state := stateMap.set state .instr_lb (load && decide (funct3 word = 0))
  let state := stateMap.set state .instr_lh (load && decide (funct3 word = 1))
  let state := stateMap.set state .instr_lw (load && decide (funct3 word = 2))
  let state := stateMap.set state .instr_lbu (load && decide (funct3 word = 4))
  let state := stateMap.set state .instr_lhu (load && decide (funct3 word = 5))
  let state := stateMap.set state .instr_sb (store && decide (funct3 word = 0))
  let state := stateMap.set state .instr_sh (store && decide (funct3 word = 1))
  let state := stateMap.set state .instr_sw (store && decide (funct3 word = 2))
  let state := stateMap.set state .instr_addi (imm && decide (funct3 word = 0))
  let state := stateMap.set state .instr_slti (imm && decide (funct3 word = 2))
  let state := stateMap.set state .instr_sltiu (imm && decide (funct3 word = 3))
  let state := stateMap.set state .instr_xori (imm && decide (funct3 word = 4))
  let state := stateMap.set state .instr_ori (imm && decide (funct3 word = 6))
  let state := stateMap.set state .instr_andi (imm && decide (funct3 word = 7))
  let state := stateMap.set state .instr_slli
    (imm && decide (funct3 word = 1 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srli
    (imm && decide (funct3 word = 5 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srai
    (imm && decide (funct3 word = 5 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_add
    (reg && decide (funct3 word = 0 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sub
    (reg && decide (funct3 word = 0 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_sll
    (reg && decide (funct3 word = 1 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_slt
    (reg && decide (funct3 word = 2 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sltu
    (reg && decide (funct3 word = 3 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_xor
    (reg && decide (funct3 word = 4 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srl
    (reg && decide (funct3 word = 5 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sra
    (reg && decide (funct3 word = 5 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_or
    (reg && decide (funct3 word = 6 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_and
    (reg && decide (funct3 word = 7 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_ecall_ebreak
    (decide (opcode word = 0x73 ∧ field word 21 11 = 0 ∧ field word 7 13 = 0))
  let state := stateMap.set state .instr_fence
    (decide (opcode word = 0x0f ∧ funct3 word = 0))
  let state := stateMap.set state .is_slli_srli_srai
    (imm && decide ((funct3 word = 1 ∧ funct7 word = 0) ∨
      (funct3 word = 5 ∧ (funct7 word = 0 ∨ funct7 word = 0x20))))
  let state := stateMap.set state .is_jalr_addi_slti_sltiu_xori_ori_andi
    (inputs.instr_jalr || (imm && decide (funct3 word = 0 ∨ funct3 word = 2 ∨
      funct3 word = 3 ∨ funct3 word = 4 ∨ funct3 word = 6 ∨ funct3 word = 7)))
  let state := stateMap.set state .is_sll_srl_sra
    (reg && decide ((funct3 word = 1 ∧ funct7 word = 0) ∨
      (funct3 word = 5 ∧ (funct7 word = 0 ∨ funct7 word = 0x20))))
  let state := stateMap.set state .is_lui_auipc_jal_jalr_addi_add_sub false
  let state := stateMap.set state .is_compare false
  let decodedImm :=
    if inputs.instr_jal then inputs.decoded_imm_j
    else if inputs.instr_lui || inputs.instr_auipc then immediateU word
    else if inputs.instr_jalr || load || imm then immediateI word
    else if branch then immediateB word
    else if store then immediateS word
    else current .decoded_imm
  stateMap.set state .decoded_imm decodedImm

def resetApplied (resetn : Bool) (state : stateMap.Values) : stateMap.Values :=
  if resetn then state else
  let state := stateMap.set state .is_compare false
  let state := stateMap.set state .instr_beq false
  let state := stateMap.set state .instr_bne false
  let state := stateMap.set state .instr_blt false
  let state := stateMap.set state .instr_bge false
  let state := stateMap.set state .instr_bltu false
  let state := stateMap.set state .instr_bgeu false
  let state := stateMap.set state .instr_addi false
  let state := stateMap.set state .instr_slti false
  let state := stateMap.set state .instr_sltiu false
  let state := stateMap.set state .instr_xori false
  let state := stateMap.set state .instr_ori false
  let state := stateMap.set state .instr_andi false
  let state := stateMap.set state .instr_add false
  let state := stateMap.set state .instr_sub false
  let state := stateMap.set state .instr_sll false
  let state := stateMap.set state .instr_slt false
  let state := stateMap.set state .instr_sltu false
  let state := stateMap.set state .instr_xor false
  let state := stateMap.set state .instr_srl false
  let state := stateMap.set state .instr_sra false
  let state := stateMap.set state .instr_or false
  let state := stateMap.set state .instr_and false
  stateMap.set state .instr_fence false

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  resetApplied inputs.resetn (decoded inputs state (summarized inputs state))

def recognized (inputs : Inputs) (state : stateMap.Values) : Bool := boolOr [
  inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal, inputs.instr_jalr,
  state .instr_beq, state .instr_bne, state .instr_blt, state .instr_bge,
  state .instr_bltu, state .instr_bgeu, state .instr_lb, state .instr_lh,
  state .instr_lw, state .instr_lbu, state .instr_lhu, state .instr_sb,
  state .instr_sh, state .instr_sw, state .instr_addi, state .instr_slti,
  state .instr_sltiu, state .instr_xori, state .instr_ori, state .instr_andi,
  state .instr_slli, state .instr_srli, state .instr_srai, state .instr_add,
  state .instr_sub, state .instr_sll, state .instr_slt, state .instr_sltu,
  state .instr_xor, state .instr_srl, state .instr_sra, state .instr_or,
  state .instr_and, state .instr_ecall_ebreak, state .instr_fence]

def outputValues (inputs : Inputs) (state : stateMap.Values) : outputMap.Values
  | .instr_trap => !(recognized inputs state)
  | .instr_beq => state .instr_beq | .instr_bne => state .instr_bne
  | .instr_blt => state .instr_blt | .instr_bge => state .instr_bge
  | .instr_bltu => state .instr_bltu | .instr_bgeu => state .instr_bgeu
  | .instr_lb => state .instr_lb | .instr_lh => state .instr_lh
  | .instr_lw => state .instr_lw | .instr_lbu => state .instr_lbu
  | .instr_lhu => state .instr_lhu
  | .instr_sb => state .instr_sb | .instr_sh => state .instr_sh
  | .instr_sw => state .instr_sw
  | .instr_addi => state .instr_addi | .instr_slti => state .instr_slti
  | .instr_sltiu => state .instr_sltiu | .instr_xori => state .instr_xori
  | .instr_ori => state .instr_ori | .instr_andi => state .instr_andi
  | .instr_slli => state .instr_slli | .instr_srli => state .instr_srli
  | .instr_srai => state .instr_srai
  | .instr_add => state .instr_add | .instr_sub => state .instr_sub
  | .instr_sll => state .instr_sll | .instr_slt => state .instr_slt
  | .instr_sltu => state .instr_sltu | .instr_xor => state .instr_xor
  | .instr_srl => state .instr_srl | .instr_sra => state .instr_sra
  | .instr_or => state .instr_or | .instr_and => state .instr_and
  | .instr_fence => state .instr_fence
  | .decoded_imm => state .decoded_imm
  | .is_lui_auipc_jal => state .is_lui_auipc_jal
  | .is_slli_srli_srai => state .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      state .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => state .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      state .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => state .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => state .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => state .is_lbu_lhu_lw
  | .is_compare => state .is_compare

namespace OutputRule
inductive Input | instr_lui | instr_auipc | instr_jal | instr_jalr
deriving Enumeration
end OutputRule

@[reducible] private def outputInputsGroup : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap OutputRule.Input fun
    | .instr_lui => .instr_lui
    | .instr_auipc => .instr_auipc
    | .instr_jal => .instr_jal
    | .instr_jalr => .instr_jalr

def outputInputs (instr_lui instr_auipc instr_jal instr_jalr : Bool) : Inputs :=
  { resetn := true
    decoder_trigger := false
    decoder_pseudo_trigger := false
    mem_rdata_q := wordOfNat 0
    instr_lui, instr_auipc, instr_jal, instr_jalr
    decoded_imm_j := wordOfNat 0
    is_beq_bne_blt_bge_bltu_bgeu := false
    is_lb_lh_lw_lbu_lhu := false
    is_sb_sh_sw := false
    is_alu_reg_imm := false
    is_alu_reg_reg := false }

theorem outputValues_depends_only_on_instruction_flags
    (inputs : Inputs) (state : stateMap.Values) :
    outputValues (outputInputs inputs.instr_lui inputs.instr_auipc
      inputs.instr_jal inputs.instr_jalr) state = outputValues inputs state := by
  funext output
  cases output <;> rfl

def outputRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := outputInputsGroup
  writesOutputs := .all outputMap
  target inputs state := outputValues
    (outputInputs (inputs .instr_lui) (inputs .instr_auipc)
      (inputs .instr_jal) (inputs .instr_jalr)) state

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (valuesOf inputs) state

@[simp] theorem outputRule_reads (input : Input) :
    input ∈ outputRule.readsInputs.labels ↔
      input = .instr_lui ∨ input = .instr_auipc ∨ input = .instr_jal ∨
        input = .instr_jalr := by
  change input ∈ outputInputsGroup.labels ↔ _
  letI : DecidableEq Input := inputMap.labels.decidableEq
  cases input <;> decide

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (SignalGroup.all outputMap).labels
  rw [SignalGroup.all_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem stateRule_reads (input : Input) :
    input ∈ stateRule.readsInputs.labels := by
  change input ∈ (SignalGroup.all inputMap).labels
  rw [SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues (valuesOf inputs) state := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  change outputs = outputValues
      (outputInputs (valuesOf inputs).instr_lui (valuesOf inputs).instr_auipc
        (valuesOf inputs).instr_jal (valuesOf inputs).instr_jalr) state ↔ _
  rw [outputValues_depends_only_on_instruction_flags (valuesOf inputs) state]

end Silean.Examples.PicoRV.Decoder.ResolveStage
