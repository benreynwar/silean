import PicoRV.Decoder.DecoderCaptureStage
import PicoRV.Decoder.DecoderResolveStage
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

namespace PicoRV.Decoder

open Silean
open Silean.Authoring

/-! Exact cycle contract for the two-stage registered instruction decoder in
the selected RV32I PicoRV32 configuration. The first stage captures opcode
classes, register addresses, and the J immediate when an instruction response
completes. The second stage resolves funct fields and the remaining immediate
on `decoder_trigger && !decoder_pseudo_trigger`. Summary flags follow the
source's nonblocking-assignment timing and therefore observe the previous
cycle's detailed flags.

Disabled counters, compressed instructions, IRQs, and PCPI operations are not
ports of this specialized decoder. `compressed_instr` remains because the
control region consumes that source signal; every captured instruction sets it
to false. Most decoder registers are intentionally not reset by PicoRV32, so
their pre-decode values remain unconstrained contract state. -/

module_ports ports where
  input resetn : .bit,
  input mem_do_rinst : .bit,
  input mem_done : .bit,
  input mem_rdata_latched : .vector 32 .bit,
  input decoder_trigger : .bit,
  input decoder_pseudo_trigger : .bit,
  input mem_rdata_q : .vector 32 .bit,
  output instr_trap : .bit,
  output instr_lui : .bit,
  output instr_jal : .bit,
  output instr_jalr : .bit,
  output instr_beq : .bit,
  output instr_bne : .bit,
  output instr_bge : .bit,
  output instr_bgeu : .bit,
  output instr_lb : .bit,
  output instr_lh : .bit,
  output instr_lw : .bit,
  output instr_lbu : .bit,
  output instr_lhu : .bit,
  output instr_sb : .bit,
  output instr_sh : .bit,
  output instr_sw : .bit,
  output instr_xori : .bit,
  output instr_ori : .bit,
  output instr_andi : .bit,
  output instr_slli : .bit,
  output instr_srli : .bit,
  output instr_srai : .bit,
  output instr_sub : .bit,
  output instr_sll : .bit,
  output instr_xor : .bit,
  output instr_srl : .bit,
  output instr_sra : .bit,
  output instr_or : .bit,
  output instr_and : .bit,
  output decoded_rd : .vector 5 .bit,
  output decoded_rs1 : .vector 5 .bit,
  output decoded_rs2 : .vector 5 .bit,
  output decoded_imm : .vector 32 .bit,
  output decoded_imm_j : .vector 32 .bit,
  output is_lui_auipc_jal : .bit,
  output is_lb_lh_lw_lbu_lhu : .bit,
  output is_slli_srli_srai : .bit,
  output is_jalr_addi_slti_sltiu_xori_ori_andi : .bit,
  output is_sb_sh_sw : .bit,
  output is_sll_srl_sra : .bit,
  output is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  output is_slti_blt_slt : .bit,
  output is_sltiu_bltu_sltu : .bit,
  output is_beq_bne_blt_bge_bltu_bgeu : .bit,
  output is_lbu_lhu_lw : .bit,
  output is_compare : .bit

inductive Register
  | instr_lui | instr_auipc | instr_jal | instr_jalr
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
  | decoded_rd | decoded_rs1 | decoded_rs2 | decoded_imm | decoded_imm_j
  | compressed_instr
  | is_lui_auipc_jal | is_lb_lh_lw_lbu_lhu | is_slli_srli_srai
  | is_jalr_addi_slti_sltiu_xori_ori_andi | is_sb_sh_sw | is_sll_srl_sra
  | is_lui_auipc_jal_jalr_addi_add_sub | is_slti_blt_slt
  | is_sltiu_bltu_sltu | is_beq_bne_blt_bge_bltu_bgeu
  | is_lbu_lhu_lw | is_alu_reg_imm | is_alu_reg_reg | is_compare
deriving Enumeration

def registerType : Register → SignalType
  | .decoded_rd | .decoded_rs1 | .decoded_rs2 => .vector 5 .bit
  | .decoded_imm | .decoded_imm_j => .vector 32 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := Silean.EnumeratedMap.of Register registerType

structure Inputs where
  resetn : Bool
  mem_do_rinst : Bool
  mem_done : Bool
  mem_rdata_latched : Word
  decoder_trigger : Bool
  decoder_pseudo_trigger : Bool
  mem_rdata_q : Word

def valuesOf (inputs : ports.inputs.Values) : Inputs where
  resetn := inputs .resetn
  mem_do_rinst := inputs .mem_do_rinst
  mem_done := inputs .mem_done
  mem_rdata_latched := inputs .mem_rdata_latched
  decoder_trigger := inputs .decoder_trigger
  decoder_pseudo_trigger := inputs .decoder_pseudo_trigger
  mem_rdata_q := inputs .mem_rdata_q

def summarized (state : stateMap.Values) : stateMap.Values :=
  let state := stateMap.set state .is_lui_auipc_jal
    (boolOr [state .instr_lui, state .instr_auipc, state .instr_jal])
  let state := stateMap.set state .is_lui_auipc_jal_jalr_addi_add_sub
    (boolOr [state .instr_lui, state .instr_auipc, state .instr_jal,
      state .instr_jalr, state .instr_addi, state .instr_add, state .instr_sub])
  let state := stateMap.set state .is_slti_blt_slt
    (boolOr [state .instr_slti, state .instr_blt, state .instr_slt])
  let state := stateMap.set state .is_sltiu_bltu_sltu
    (boolOr [state .instr_sltiu, state .instr_bltu, state .instr_sltu])
  let state := stateMap.set state .is_lbu_lhu_lw
    (boolOr [state .instr_lbu, state .instr_lhu, state .instr_lw])
  stateMap.set state .is_compare
    (boolOr [state .is_beq_bne_blt_bge_bltu_bgeu,
      state .instr_slti, state .instr_slt, state .instr_sltiu, state .instr_sltu])

def captured (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  if !(inputs.mem_do_rinst && inputs.mem_done) then state else
  let word := inputs.mem_rdata_latched
  let state := stateMap.set state .instr_lui (decide (opcode word = 0x37))
  let state := stateMap.set state .instr_auipc (decide (opcode word = 0x17))
  let state := stateMap.set state .instr_jal (decide (opcode word = 0x6f))
  let state := stateMap.set state .instr_jalr (decide (opcode word = 0x67 ∧ funct3 word = 0))
  let state := stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu (decide (opcode word = 0x63))
  let state := stateMap.set state .is_lb_lh_lw_lbu_lhu (decide (opcode word = 0x03))
  let state := stateMap.set state .is_sb_sh_sw (decide (opcode word = 0x23))
  let state := stateMap.set state .is_alu_reg_imm (decide (opcode word = 0x13))
  let state := stateMap.set state .is_alu_reg_reg (decide (opcode word = 0x33))
  let state := stateMap.set state .decoded_rd (addressOfNat (field word 7 5))
  let state := stateMap.set state .decoded_rs1 (addressOfNat (field word 15 5))
  let state := stateMap.set state .decoded_rs2 (addressOfNat (field word 20 5))
  let state := stateMap.set state .decoded_imm_j (immediateJ word)
  stateMap.set state .compressed_instr false

def decoded (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  if !(inputs.decoder_trigger && !inputs.decoder_pseudo_trigger) then updated else
  let word := inputs.mem_rdata_q
  let branch : Bool := current .is_beq_bne_blt_bge_bltu_bgeu
  let load : Bool := current .is_lb_lh_lw_lbu_lhu
  let store : Bool := current .is_sb_sh_sw
  let imm : Bool := current .is_alu_reg_imm
  let reg : Bool := current .is_alu_reg_reg
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
  let state := stateMap.set state .instr_slli (imm && decide (funct3 word = 1 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srli (imm && decide (funct3 word = 5 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srai (imm && decide (funct3 word = 5 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_add (reg && decide (funct3 word = 0 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sub (reg && decide (funct3 word = 0 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_sll (reg && decide (funct3 word = 1 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_slt (reg && decide (funct3 word = 2 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sltu (reg && decide (funct3 word = 3 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_xor (reg && decide (funct3 word = 4 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_srl (reg && decide (funct3 word = 5 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_sra (reg && decide (funct3 word = 5 ∧ funct7 word = 0x20))
  let state := stateMap.set state .instr_or (reg && decide (funct3 word = 6 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_and (reg && decide (funct3 word = 7 ∧ funct7 word = 0))
  let state := stateMap.set state .instr_ecall_ebreak
    (decide (opcode word = 0x73 ∧ field word 21 11 = 0 ∧ field word 7 13 = 0))
  let state := stateMap.set state .instr_fence (decide (opcode word = 0x0f ∧ funct3 word = 0))
  let state := stateMap.set state .is_slli_srli_srai
    (imm && decide ((funct3 word = 1 ∧ funct7 word = 0) ∨
      (funct3 word = 5 ∧ (funct7 word = 0 ∨ funct7 word = 0x20))))
  let state := stateMap.set state .is_jalr_addi_slti_sltiu_xori_ori_andi
    (current .instr_jalr || (imm && decide (funct3 word = 0 ∨ funct3 word = 2 ∨
      funct3 word = 3 ∨ funct3 word = 4 ∨ funct3 word = 6 ∨ funct3 word = 7)))
  let state := stateMap.set state .is_sll_srl_sra
    (reg && decide ((funct3 word = 1 ∧ funct7 word = 0) ∨
      (funct3 word = 5 ∧ (funct7 word = 0 ∨ funct7 word = 0x20))))
  let state := stateMap.set state .is_lui_auipc_jal_jalr_addi_add_sub false
  let state := stateMap.set state .is_compare false
  let jal : Bool := current .instr_jal
  let upper : Bool := current .instr_lui || current .instr_auipc
  let immediateClass : Bool := current .instr_jalr || load || imm
  let decodedImm :=
    if jal then current .decoded_imm_j
    else if upper then immediateU word
    else if immediateClass then immediateI word
    else if branch then immediateB word
    else if store then immediateS word
    else current .decoded_imm
  stateMap.set state .decoded_imm decodedImm

def resetApplied (resetn : Bool) (state : stateMap.Values) : stateMap.Values :=
  if resetn then state else
  let state := stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu false
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

def captureState (state : stateMap.Values) : CaptureStage.stateMap.Values
  | .instr_lui => state .instr_lui | .instr_auipc => state .instr_auipc
  | .instr_jal => state .instr_jal | .instr_jalr => state .instr_jalr
  | .decoded_rd => state .decoded_rd | .decoded_rs1 => state .decoded_rs1
  | .decoded_rs2 => state .decoded_rs2 | .decoded_imm_j => state .decoded_imm_j
  | .compressed_instr => state .compressed_instr
  | .is_beq_bne_blt_bge_bltu_bgeu => state .is_beq_bne_blt_bge_bltu_bgeu
  | .is_lb_lh_lw_lbu_lhu => state .is_lb_lh_lw_lbu_lhu
  | .is_sb_sh_sw => state .is_sb_sh_sw
  | .is_alu_reg_imm => state .is_alu_reg_imm
  | .is_alu_reg_reg => state .is_alu_reg_reg

def resolveState (state : stateMap.Values) : ResolveStage.stateMap.Values
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
  | .instr_ecall_ebreak => state .instr_ecall_ebreak
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

def mergeState (capture : CaptureStage.stateMap.Values)
    (resolve : ResolveStage.stateMap.Values) : stateMap.Values
  | .instr_lui => capture .instr_lui | .instr_auipc => capture .instr_auipc
  | .instr_jal => capture .instr_jal | .instr_jalr => capture .instr_jalr
  | .instr_beq => resolve .instr_beq | .instr_bne => resolve .instr_bne
  | .instr_blt => resolve .instr_blt | .instr_bge => resolve .instr_bge
  | .instr_bltu => resolve .instr_bltu | .instr_bgeu => resolve .instr_bgeu
  | .instr_lb => resolve .instr_lb | .instr_lh => resolve .instr_lh
  | .instr_lw => resolve .instr_lw | .instr_lbu => resolve .instr_lbu
  | .instr_lhu => resolve .instr_lhu
  | .instr_sb => resolve .instr_sb | .instr_sh => resolve .instr_sh
  | .instr_sw => resolve .instr_sw
  | .instr_addi => resolve .instr_addi | .instr_slti => resolve .instr_slti
  | .instr_sltiu => resolve .instr_sltiu | .instr_xori => resolve .instr_xori
  | .instr_ori => resolve .instr_ori | .instr_andi => resolve .instr_andi
  | .instr_slli => resolve .instr_slli | .instr_srli => resolve .instr_srli
  | .instr_srai => resolve .instr_srai
  | .instr_add => resolve .instr_add | .instr_sub => resolve .instr_sub
  | .instr_sll => resolve .instr_sll | .instr_slt => resolve .instr_slt
  | .instr_sltu => resolve .instr_sltu | .instr_xor => resolve .instr_xor
  | .instr_srl => resolve .instr_srl | .instr_sra => resolve .instr_sra
  | .instr_or => resolve .instr_or | .instr_and => resolve .instr_and
  | .instr_ecall_ebreak => resolve .instr_ecall_ebreak
  | .instr_fence => resolve .instr_fence
  | .decoded_rd => capture .decoded_rd | .decoded_rs1 => capture .decoded_rs1
  | .decoded_rs2 => capture .decoded_rs2 | .decoded_imm => resolve .decoded_imm
  | .decoded_imm_j => capture .decoded_imm_j
  | .compressed_instr => capture .compressed_instr
  | .is_lui_auipc_jal => resolve .is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => capture .is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => resolve .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      resolve .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sb_sh_sw => capture .is_sb_sh_sw
  | .is_sll_srl_sra => resolve .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      resolve .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => resolve .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => resolve .is_sltiu_bltu_sltu
  | .is_beq_bne_blt_bge_bltu_bgeu => capture .is_beq_bne_blt_bge_bltu_bgeu
  | .is_lbu_lhu_lw => resolve .is_lbu_lhu_lw
  | .is_alu_reg_imm => capture .is_alu_reg_imm
  | .is_alu_reg_reg => capture .is_alu_reg_reg
  | .is_compare => resolve .is_compare

@[simp] theorem captureState_mergeState (capture : CaptureStage.stateMap.Values)
    (resolve : ResolveStage.stateMap.Values) :
    captureState (mergeState capture resolve) = capture := by
  funext register
  cases register <;> rfl

@[simp] theorem resolveState_mergeState (capture : CaptureStage.stateMap.Values)
    (resolve : ResolveStage.stateMap.Values) :
    resolveState (mergeState capture resolve) = resolve := by
  funext register
  cases register <;> rfl

def captureInputs (inputs : Inputs) : CaptureStage.Inputs where
  resetn := inputs.resetn
  mem_do_rinst := inputs.mem_do_rinst
  mem_done := inputs.mem_done
  mem_rdata_latched := inputs.mem_rdata_latched

def resolveInputs (inputs : Inputs) (capture : CaptureStage.stateMap.Values) :
    ResolveStage.Inputs where
  resetn := inputs.resetn
  decoder_trigger := inputs.decoder_trigger
  decoder_pseudo_trigger := inputs.decoder_pseudo_trigger
  mem_rdata_q := inputs.mem_rdata_q
  instr_lui := capture .instr_lui
  instr_auipc := capture .instr_auipc
  instr_jal := capture .instr_jal
  instr_jalr := capture .instr_jalr
  decoded_imm_j := capture .decoded_imm_j
  is_beq_bne_blt_bge_bltu_bgeu := capture .is_beq_bne_blt_bge_bltu_bgeu
  is_lb_lh_lw_lbu_lhu := capture .is_lb_lh_lw_lbu_lhu
  is_sb_sh_sw := capture .is_sb_sh_sw
  is_alu_reg_imm := capture .is_alu_reg_imm
  is_alu_reg_reg := capture .is_alu_reg_reg

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let capture := captureState state
  mergeState
    (CaptureStage.nextState (captureInputs inputs) capture)
    (ResolveStage.nextState (resolveInputs inputs capture) (resolveState state))

def recognized (state : stateMap.Values) : Bool := boolOr [
  state .instr_lui, state .instr_auipc, state .instr_jal, state .instr_jalr,
  state .instr_beq, state .instr_bne, state .instr_blt, state .instr_bge,
  state .instr_bltu, state .instr_bgeu, state .instr_lb, state .instr_lh,
  state .instr_lw, state .instr_lbu, state .instr_lhu, state .instr_sb,
  state .instr_sh, state .instr_sw, state .instr_addi, state .instr_slti,
  state .instr_sltiu, state .instr_xori, state .instr_ori, state .instr_andi,
  state .instr_slli, state .instr_srli, state .instr_srai, state .instr_add,
  state .instr_sub, state .instr_sll, state .instr_slt, state .instr_sltu,
  state .instr_xor, state .instr_srl, state .instr_sra, state .instr_or,
  state .instr_and, state .instr_fence]

def outputValues (state : stateMap.Values) : outputMap.Values
  | .instr_trap => !(recognized state)
  | .instr_lui => state .instr_lui
  | .instr_jal => state .instr_jal
  | .instr_jalr => state .instr_jalr
  | .instr_beq => state .instr_beq
  | .instr_bne => state .instr_bne
  | .instr_bge => state .instr_bge
  | .instr_bgeu => state .instr_bgeu
  | .instr_lb => state .instr_lb
  | .instr_lh => state .instr_lh
  | .instr_lw => state .instr_lw
  | .instr_lbu => state .instr_lbu
  | .instr_lhu => state .instr_lhu
  | .instr_sb => state .instr_sb
  | .instr_sh => state .instr_sh
  | .instr_sw => state .instr_sw
  | .instr_xori => state .instr_xori
  | .instr_ori => state .instr_ori
  | .instr_andi => state .instr_andi
  | .instr_slli => state .instr_slli
  | .instr_srli => state .instr_srli
  | .instr_srai => state .instr_srai
  | .instr_sub => state .instr_sub
  | .instr_sll => state .instr_sll
  | .instr_xor => state .instr_xor
  | .instr_srl => state .instr_srl
  | .instr_sra => state .instr_sra
  | .instr_or => state .instr_or
  | .instr_and => state .instr_and
  | .decoded_rd => state .decoded_rd
  | .decoded_rs1 => state .decoded_rs1
  | .decoded_rs2 => state .decoded_rs2
  | .decoded_imm => state .decoded_imm
  | .decoded_imm_j => state .decoded_imm_j
  | .is_lui_auipc_jal => state .is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => state .is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => state .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      state .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sb_sh_sw => state .is_sb_sh_sw
  | .is_sll_srl_sra => state .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      state .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => state .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => state .is_sltiu_bltu_sltu
  | .is_beq_bne_blt_bge_bltu_bgeu => state .is_beq_bne_blt_bge_bltu_bgeu
  | .is_lbu_lhu_lw => state .is_lbu_lhu_lw
  | .is_compare => state .is_compare

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := .all outputMap
  target := fun _ state => outputValues state

def stateRule : Silean.Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (valuesOf inputs) state

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues state := by
  simp [outputRule, Silean.Contracts.Cycle.CycleOutputRule.Holds]

end PicoRV.Decoder
