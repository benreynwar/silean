import Silean.Examples.PicoRV.Control

namespace Silean.Examples.Fixtures.PicoRVControl

open Silean
open Silean.Examples.PicoRV.Control

/-- Neutral control inputs used as a readable base for focused transition checks. -/
def idleInputs : Inputs where
  resetn := true
  instr_jal := false
  instr_jalr := false
  instr_lb := false
  instr_lbu := false
  instr_lh := false
  instr_lhu := false
  instr_lw := false
  instr_sb := false
  instr_sh := false
  instr_sw := false
  instr_trap := false
  is_lui_auipc_jal := false
  is_lb_lh_lw_lbu_lhu := false
  is_slli_srli_srai := false
  is_jalr_addi_slti_sltiu_xori_ori_andi := false
  is_sb_sh_sw := false
  is_sll_srl_sra := false
  is_beq_bne_blt_bge_bltu_bgeu := false
  is_lbu_lhu_lw := false
  decoded_rd := fiveBitsOfNat 0
  reg_pc := wordOfNat 0
  reg_op1 := wordOfNat 0
  reg_sh := fiveBitsOfNat 0
  alu_out_0 := false
  mem_done := false

def initialState : stateMap.Values := stateMap.defaultValues

def stateIn (cpuPhase : Nat) : stateMap.Values :=
  stateMap.set initialState .cpu_state (stateBits cpuPhase)

def commandState (cpuPhase : Nat) (prefetch rinst rdata wdata : Bool) :
    stateMap.Values :=
  let state := stateIn cpuPhase
  let state := stateMap.set state .mem_do_prefetch prefetch
  let state := stateMap.set state .mem_do_rinst rinst
  let state := stateMap.set state .mem_do_rdata rdata
  stateMap.set state .mem_do_wdata wdata

end Silean.Examples.Fixtures.PicoRVControl
