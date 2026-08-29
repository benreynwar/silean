import Silean.Examples.PicoRV.Datapath

namespace Silean.Examples.Checks.PicoRVDatapathFixtures

open Silean
open Silean.Examples.PicoRV.Datapath

def idleInputs : Inputs where
  resetn := true
  cpu_state := stateBits cpuStateTrap
  latched_store := false
  latched_stalu := false
  latched_branch := false
  latched_is_lu := false
  latched_is_lh := false
  latched_is_lb := false
  mem_do_prefetch := false
  mem_do_rdata := false
  mem_do_wdata := false
  decoder_trigger := false
  instr_lui := false
  instr_jal := false
  instr_sub := false
  instr_beq := false
  instr_bne := false
  instr_bge := false
  instr_bgeu := false
  instr_xori := false
  instr_xor := false
  instr_ori := false
  instr_or := false
  instr_andi := false
  instr_and := false
  instr_slli := false
  instr_srli := false
  instr_srai := false
  instr_sll := false
  instr_srl := false
  instr_sra := false
  is_lui_auipc_jal := false
  is_lb_lh_lw_lbu_lhu := false
  is_slli_srli_srai := false
  is_jalr_addi_slti_sltiu_xori_ori_andi := false
  is_lui_auipc_jal_jalr_addi_add_sub := false
  is_slti_blt_slt := false
  is_sltiu_bltu_sltu := false
  is_compare := false
  decoded_imm := wordOfNat 0
  decoded_imm_j := wordOfNat 0
  decoded_rs2 := fiveBitsOfNat 0
  cpuregs_rs1 := wordOfNat 0
  cpuregs_rs2 := wordOfNat 0
  mem_done := false
  mem_rdata_word := wordOfNat 0

def initialState : stateMap.Values := stateMap.defaultValues

def stateWith (pc nextPc op1 op2 result shift aluQ : Nat) : stateMap.Values :=
  let state := stateMap.set initialState .reg_pc (wordOfNat pc)
  let state := stateMap.set state .reg_next_pc (wordOfNat nextPc)
  let state := stateMap.set state .reg_op1 (wordOfNat op1)
  let state := stateMap.set state .reg_op2 (wordOfNat op2)
  let state := stateMap.set state .reg_out (wordOfNat result)
  let state := stateMap.set state .reg_sh (fiveBitsOfNat shift)
  stateMap.set state .alu_out_q (wordOfNat aluQ)

end Silean.Examples.Checks.PicoRVDatapathFixtures
