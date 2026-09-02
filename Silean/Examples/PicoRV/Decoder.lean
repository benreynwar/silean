import Silean.Examples.PicoRV.Decoder.DecoderCaptureStage
import Silean.Examples.PicoRV.Decoder.DecoderResolveStage
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Contracts.Cycle.CycleBlackbox

namespace Silean.Examples.PicoRV.Decoder

open Silean

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

inductive Input
  | resetn
  | mem_do_rinst
  | mem_done
  | mem_rdata_latched
  | decoder_trigger
  | decoder_pseudo_trigger
  | mem_rdata_q
deriving Enumeration

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

/-! Only signals read outside the decoder are ports. Other decode registers
remain private state because they feed summary flags or `instr_trap` locally. -/
inductive Output
  | instr_trap
  | instr_lui | instr_jal | instr_jalr
  | instr_beq | instr_bne | instr_bge | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_sub | instr_sll | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | decoded_rd | decoded_rs1 | decoded_rs2 | decoded_imm | decoded_imm_j
  | is_lui_auipc_jal | is_lb_lh_lw_lbu_lhu | is_slli_srli_srai
  | is_jalr_addi_slti_sltiu_xori_ori_andi | is_sb_sh_sw | is_sll_srl_sra
  | is_lui_auipc_jal_jalr_addi_add_sub | is_slti_blt_slt
  | is_sltiu_bltu_sltu | is_beq_bne_blt_bge_bltu_bgeu
  | is_lbu_lhu_lw | is_compare
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .mem_rdata_latched | .mem_rdata_q => .vector 32 .bit
    | _ => .bit

def registerType : Register → SignalType
  | .decoded_rd | .decoded_rs1 | .decoded_rs2 => .vector 5 .bit
  | .decoded_imm | .decoded_imm_j => .vector 32 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of Register registerType

def outputType : Output → SignalType
  | .decoded_rd | .decoded_rs1 | .decoded_rs2 => .vector 5 .bit
  | .decoded_imm | .decoded_imm_j => .vector 32 .bit
  | _ => .bit

@[reducible] def outputMap : SignalMap := EnumeratedMap.of Output outputType

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

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
  state .instr_and, state .instr_ecall_ebreak, state .instr_fence]

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

inductive Rule | outputs
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .nil, outputTypes := .ofList outputMap.types } where
  readsInputs := .nil
  writesOutputs := outputMap.allSelection
  target := fun _ state => outputMap.allSelection.project (outputValues state)

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  inputTypes := .cons .bit (.cons .bit (.cons .bit (.cons (.vector 32 .bit)
    (.cons .bit (.cons .bit (.cons (.vector 32 .bit) .nil))))))
  readsInputs := ((((((inputMap.select .mem_rdata_q).prepend .decoder_pseudo_trigger).prepend
    .decoder_trigger).prepend .mem_rdata_latched).prepend .mem_done).prepend
    .mem_do_rinst).prepend .resetn
  target
    | (resetn, (mem_do_rinst, (mem_done, (mem_rdata_latched,
        (decoder_trigger, (decoder_pseudo_trigger, (mem_rdata_q, ()))))))), state =>
      nextState ⟨resetn, mem_do_rinst, mem_done, mem_rdata_latched,
        decoder_trigger, decoder_pseudo_trigger, mem_rdata_q⟩ state

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .outputs => ⟨_, outputRule⟩
  stateRule := stateRule
  outputCoverage := by
    change outputMap.allSelection.labels.Perm outputMap.labels.values
    rw [SignalMap.allSelection_labels]

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues state := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.allSelection_matches_project_iff]

/-! ## Two-stage structural decomposition -/

inductive Instance | capture | resolve
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .capture => CaptureStage.ports
    | .resolve => ResolveStage.ports

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput := fun
    | .instr_trap => context.instanceOutput .resolve .instr_trap
    | .instr_lui => context.instanceOutput .capture .instr_lui
    | .instr_jal => context.instanceOutput .capture .instr_jal
    | .instr_jalr => context.instanceOutput .capture .instr_jalr
    | .instr_beq => context.instanceOutput .resolve .instr_beq
    | .instr_bne => context.instanceOutput .resolve .instr_bne
    | .instr_bge => context.instanceOutput .resolve .instr_bge
    | .instr_bgeu => context.instanceOutput .resolve .instr_bgeu
    | .instr_lb => context.instanceOutput .resolve .instr_lb
    | .instr_lh => context.instanceOutput .resolve .instr_lh
    | .instr_lw => context.instanceOutput .resolve .instr_lw
    | .instr_lbu => context.instanceOutput .resolve .instr_lbu
    | .instr_lhu => context.instanceOutput .resolve .instr_lhu
    | .instr_sb => context.instanceOutput .resolve .instr_sb
    | .instr_sh => context.instanceOutput .resolve .instr_sh
    | .instr_sw => context.instanceOutput .resolve .instr_sw
    | .instr_xori => context.instanceOutput .resolve .instr_xori
    | .instr_ori => context.instanceOutput .resolve .instr_ori
    | .instr_andi => context.instanceOutput .resolve .instr_andi
    | .instr_slli => context.instanceOutput .resolve .instr_slli
    | .instr_srli => context.instanceOutput .resolve .instr_srli
    | .instr_srai => context.instanceOutput .resolve .instr_srai
    | .instr_sub => context.instanceOutput .resolve .instr_sub
    | .instr_sll => context.instanceOutput .resolve .instr_sll
    | .instr_xor => context.instanceOutput .resolve .instr_xor
    | .instr_srl => context.instanceOutput .resolve .instr_srl
    | .instr_sra => context.instanceOutput .resolve .instr_sra
    | .instr_or => context.instanceOutput .resolve .instr_or
    | .instr_and => context.instanceOutput .resolve .instr_and
    | .decoded_rd => context.instanceOutput .capture .decoded_rd
    | .decoded_rs1 => context.instanceOutput .capture .decoded_rs1
    | .decoded_rs2 => context.instanceOutput .capture .decoded_rs2
    | .decoded_imm => context.instanceOutput .resolve .decoded_imm
    | .decoded_imm_j => context.instanceOutput .capture .decoded_imm_j
    | .is_lui_auipc_jal => context.instanceOutput .resolve .is_lui_auipc_jal
    | .is_lb_lh_lw_lbu_lhu => context.instanceOutput .capture .is_lb_lh_lw_lbu_lhu
    | .is_slli_srli_srai => context.instanceOutput .resolve .is_slli_srli_srai
    | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
        context.instanceOutput .resolve .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .is_sb_sh_sw => context.instanceOutput .capture .is_sb_sh_sw
    | .is_sll_srl_sra => context.instanceOutput .resolve .is_sll_srl_sra
    | .is_lui_auipc_jal_jalr_addi_add_sub =>
        context.instanceOutput .resolve .is_lui_auipc_jal_jalr_addi_add_sub
    | .is_slti_blt_slt => context.instanceOutput .resolve .is_slti_blt_slt
    | .is_sltiu_bltu_sltu => context.instanceOutput .resolve .is_sltiu_bltu_sltu
    | .is_beq_bne_blt_bge_bltu_bgeu =>
        context.instanceOutput .capture .is_beq_bne_blt_bge_bltu_bgeu
    | .is_lbu_lhu_lw => context.instanceOutput .resolve .is_lbu_lhu_lw
    | .is_compare => context.instanceOutput .resolve .is_compare
  instanceInput := fun
    | .capture, .resetn => context.moduleInput .resetn
    | .capture, .mem_do_rinst => context.moduleInput .mem_do_rinst
    | .capture, .mem_done => context.moduleInput .mem_done
    | .capture, .mem_rdata_latched => context.moduleInput .mem_rdata_latched
    | .resolve, .resetn => context.moduleInput .resetn
    | .resolve, .decoder_trigger => context.moduleInput .decoder_trigger
    | .resolve, .decoder_pseudo_trigger => context.moduleInput .decoder_pseudo_trigger
    | .resolve, .mem_rdata_q => context.moduleInput .mem_rdata_q
    | .resolve, .instr_lui => context.instanceOutput .capture .instr_lui
    | .resolve, .instr_auipc => context.instanceOutput .capture .instr_auipc
    | .resolve, .instr_jal => context.instanceOutput .capture .instr_jal
    | .resolve, .instr_jalr => context.instanceOutput .capture .instr_jalr
    | .resolve, .decoded_imm_j => context.instanceOutput .capture .decoded_imm_j
    | .resolve, .is_beq_bne_blt_bge_bltu_bgeu =>
        context.instanceOutput .capture .is_beq_bne_blt_bge_bltu_bgeu
    | .resolve, .is_lb_lh_lw_lbu_lhu =>
        context.instanceOutput .capture .is_lb_lh_lw_lbu_lhu
    | .resolve, .is_sb_sh_sw => context.instanceOutput .capture .is_sb_sh_sw
    | .resolve, .is_alu_reg_imm => context.instanceOutput .capture .is_alu_reg_imm
    | .resolve, .is_alu_reg_reg => context.instanceOutput .capture .is_alu_reg_reg

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .capture => CaptureStage.cycleContract
  | .resolve => ResolveStage.cycleContract

@[reducible] def structuralChildren :
    (child : instancePorts.Name) → ModuleStructure (instancePorts.ports child)
  | .capture => CaptureStage.moduleStructure
  | .resolve => ResolveStage.cycleContract.blackboxStructure

def moduleStructure : ModuleStructure ports := .composite body structuralChildren

@[reducible] noncomputable def certifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures body childContracts
  | .capture => CaptureStage.certified.certifiedStructure
  | .resolve => ResolveStage.cycleContract.blackboxCertified.certifiedStructure

namespace LayerCertification

open Silean.Contracts.Cycle.Certification.Layer

private abbrev captureRule : RuleOccurrence body childContracts :=
  ⟨.capture, .outputs⟩

private abbrev resolveRule : RuleOccurrence body childContracts :=
  ⟨.resolve, .outputs⟩


def scheduleOrders :
    ScheduleDerivation.RuleScheduleOrders body childContracts cycleContract where
  output := fun | .outputs => [captureRule, resolveRule]
  state := [captureRule, resolveRule]

def derivedRuleSchedules :
    ScheduleDerivation.DerivedRuleSchedules body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

abbrev ruleSchedules := derivedRuleSchedules.schedules

theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop :=
  (layerChildren .capture).certification.stateCorresponds
      (captureState contractState) (structuralState .capture) ∧
    (layerChildren .resolve).certification.stateCorresponds
      (resolveState contractState) (structuralState .resolve)

private theorem hasCorrespondingState
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .capture).certification.hasCorrespondingState
      (structuralState .capture) with ⟨capture, captureCorresponds⟩
  rcases (layerChildren .resolve).certification.hasCorrespondingState
      (structuralState .resolve) with ⟨resolve, resolveCorresponds⟩
  refine ⟨mergeState capture resolve, ?_⟩
  exact ⟨by simpa using captureCorresponds, by simpa using resolveCorresponds⟩

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have captureMatches := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .capture (captureState contractState) corresponds.1
  have resolveMatches := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .resolve (resolveState contractState) corresponds.2
  have captureOutputs : (proposal.2 .capture).outputs = captureState contractState :=
    (CaptureStage.outputRule_holds_iff _ _ _).mp
      (captureMatches.1.1 CaptureStage.Rule.outputs)
  have resolveOutputs : (proposal.2 .resolve).outputs =
      ResolveStage.outputValues (resolveInputs (valuesOf inputs)
        (captureState contractState)) (resolveState contractState) := by
    have held := (ResolveStage.outputRule_holds_iff _ _ _).mp
      (resolveMatches.1.1 ResolveStage.Rule.outputs)
    simpa [ResolveStage.valuesOf, resolveInputs, valuesOf,
      ProposedValues.childInputs_apply, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value, captureOutputs] using held
  have captureNext :
      (childContracts .capture).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .capture) (captureState contractState) =
        CaptureStage.nextState (captureInputs (valuesOf inputs))
          (captureState contractState) := by
    rfl
  have resolveNext :
      (childContracts .resolve).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .resolve) (resolveState contractState) =
        ResolveStage.nextState
          (resolveInputs (valuesOf inputs) (captureState contractState))
          (resolveState contractState) := by
    change ResolveStage.nextState
      (resolveInputs (valuesOf inputs) (proposal.2 .capture).outputs)
        (resolveState contractState) = _
    rw [captureOutputs]
  let next := nextState (valuesOf inputs) contractState
  refine ⟨next, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary : proposal.outputs output =
          (wiring.moduleOutput output).value inputs
            (fun child => (proposal.2 child).outputs) := by
        simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy] using
          satisfies.1 output
      cases output <;>
        simp only [wiring, context, EndpointContext.instanceOutput,
          SignalSource.value] at boundary <;>
        rw [boundary] <;>
        first
        | exact (congrFun captureOutputs _).trans rfl
        | exact (congrFun resolveOutputs _).trans rfl
    · change next = nextState (valuesOf inputs) contractState
      rfl
  · constructor
    · change (layerChildren .capture).certification.stateCorresponds
        (captureState next) (proposal.2 .capture).nextState
      rw [show captureState next =
          CaptureStage.nextState (captureInputs (valuesOf inputs))
            (captureState contractState) by simp [next, nextState]]
      rw [← captureNext]
      exact captureMatches.2
    · change (layerChildren .resolve).certification.stateCorresponds
        (resolveState next) (proposal.2 .resolve).nextState
      rw [show resolveState next = ResolveStage.nextState
          (resolveInputs (valuesOf inputs) (captureState contractState))
          (resolveState contractState) by simp [next, nextState]]
      rw [← resolveNext]
      exact resolveMatches.2

end Certification

end LayerCertification

noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  LayerCertification.ruleSchedules.certifiedLayer
    LayerCertification.coversChildren LayerCertification.stateCorresponds
    LayerCertification.hasCorrespondingState LayerCertification.implements

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedLayer.certifyComposite structuralChildren certifiedChildren (by
    intro child
    cases child <;> rfl)

/-- The decoder hierarchy certified against its cycle contract. The capture
stage is concrete; the resolve stage remains an explicit blackbox. -/
noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_moduleStructure :
    certified.moduleStructure = moduleStructure := rfl

@[simp] theorem certified_cycleContract :
    certified.cycleContract = cycleContract := rfl

end Silean.Examples.PicoRV.Decoder
