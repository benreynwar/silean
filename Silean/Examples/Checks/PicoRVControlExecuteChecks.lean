import Silean.Examples.Checks.PicoRVControlFixtures

namespace Silean.Examples.Checks.PicoRVControlExecuteChecks

open Silean
open Silean.Examples.PicoRV.Control
open Silean.Examples.Checks.PicoRVControlFixtures

def loadState := nextState { idleInputs with is_lb_lh_lw_lbu_lhu := true }
  (stateIn cpuStateLdRs1)
example : phase loadState = cpuStateLdmem := by decide
example : (loadState .mem_do_rinst : Bool) = true := by rfl

def illegalState := nextState { idleInputs with instr_trap := true }
  (stateIn cpuStateLdRs1)
example : phase illegalState = cpuStateTrap := by decide

def trappedState := nextState idleInputs illegalState
example : phase trappedState = cpuStateTrap := by decide
example : (trappedState .trap : Bool) = true := by rfl

def secondOperandStore := nextState { idleInputs with is_sb_sh_sw := true }
  (stateIn cpuStateLdRs2)
example : phase secondOperandStore = cpuStateStmem := by decide
example : (secondOperandStore .mem_do_rinst : Bool) = true := by rfl

def immediateState := nextState
  { idleInputs with is_jalr_addi_slti_sltiu_xori_ori_andi := true }
  (commandState cpuStateLdRs1 true false false false)
example : phase immediateState = cpuStateExec := by decide
example : (immediateState .mem_do_prefetch : Bool) = true := by rfl
example : (immediateState .mem_do_rinst : Bool) = true := by rfl

def shiftRunning := nextState { idleInputs with reg_sh := fiveBitsOfNat 5 }
  (stateIn cpuStateShift)
example : phase shiftRunning = cpuStateShift := by decide
example : (shiftRunning .latched_store : Bool) = true := by rfl

def shiftDone := nextState idleInputs
  (commandState cpuStateShift true false false false)
example : phase shiftDone = cpuStateFetch := by decide
example : (shiftDone .mem_do_prefetch : Bool) = true := by rfl
example : (shiftDone .mem_do_rinst : Bool) = true := by rfl

def takenBranch := nextState
  { idleInputs with
    is_beq_bne_blt_bge_bltu_bgeu := true
    alu_out_0 := true }
  (commandState cpuStateExec true false false false)

example : phase takenBranch = cpuStateExec := by decide
example : (takenBranch .latched_store : Bool) = true := by rfl
example : (takenBranch .latched_branch : Bool) = true := by rfl
example : (takenBranch .mem_do_prefetch : Bool) = true := by rfl
example : (takenBranch .mem_do_rinst : Bool) = true := by rfl

def completedBranch := nextState
  { idleInputs with
    is_beq_bne_blt_bge_bltu_bgeu := true
    alu_out_0 := false
    mem_done := true }
  (stateIn cpuStateExec)
example : phase completedBranch = cpuStateFetch := by decide

def jalrExecute := nextState { idleInputs with instr_jalr := true }
  (stateIn cpuStateExec)
example : phase jalrExecute = cpuStateFetch := by decide
example : (jalrExecute .latched_store : Bool) = true := by rfl
example : (jalrExecute .latched_stalu : Bool) = true := by rfl
example : (jalrExecute .latched_branch : Bool) = true := by rfl

end Silean.Examples.Checks.PicoRVControlExecuteChecks
