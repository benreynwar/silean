import Silean.Examples.Fixtures.PicoRVDatapath

namespace Silean.Examples.Checks.PicoRVDatapathFlowChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

def resetState := nextState
  { idleInputs with
    resetn := false
    is_lui_auipc_jal_jalr_addi_add_sub := true }
  (stateWith 0x1000 0x2000 3 4 5 6 7)

example : BitVector.toNat 32 (resetState .reg_pc) = 0 := by decide
example : BitVector.toNat 32 (resetState .reg_next_pc) = 0 := by decide
example : BitVector.toNat 32 (resetState .reg_op1) = 3 := by decide
example : BitVector.toNat 32 (resetState .alu_out_q) = 7 := by decide

def sequentialFetchInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateFetch, decoder_trigger := true }

def afterSequentialFetch := nextState sequentialFetchInputs
  (stateWith 0x1000 0x2000 0 0 0 0 0)

example : BitVector.toNat 32 (afterSequentialFetch .reg_pc) = 0x2000 := by decide
example : BitVector.toNat 32 (afterSequentialFetch .reg_next_pc) = 0x2004 := by decide

def jalFetchInputs : Inputs :=
  { sequentialFetchInputs with instr_jal := true, decoded_imm_j := wordOfNat 0x40 }

def afterJalFetch := nextState jalFetchInputs
  (stateWith 0x1000 0x2000 0 0 0 0 0)

example : BitVector.toNat 32 (afterJalFetch .reg_pc) = 0x2000 := by decide
example : BitVector.toNat 32 (afterJalFetch .reg_next_pc) = 0x2040 := by decide

def branchFetchInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateFetch
    latched_store := true
    latched_stalu := true
    latched_branch := true }

def branchState := stateWith 0x1000 0x2000 0 0 0x3003 0 0x4003
def afterBranchFetch := nextState branchFetchInputs branchState

example : BitVector.toNat 32 (afterBranchFetch .reg_pc) = 0x4002 := by decide
example : BitVector.toNat 32 (nextPcOutput branchFetchInputs branchState) = 0x3002 := by decide
example : BitVector.toNat 32 (writebackData branchFetchInputs branchState) = 0x1004 := by decide

def luiInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    is_lui_auipc_jal := true
    instr_lui := true
    decoded_imm := wordOfNat 0x12345000 }

def afterLui := nextState luiInputs (stateWith 0x1000 0 0 0 0 0 0)

example : BitVector.toNat 32 (afterLui .reg_op1) = 0 := by decide
example : BitVector.toNat 32 (afterLui .reg_op2) = 0x12345000 := by decide

def immediateInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    is_jalr_addi_slti_sltiu_xori_ori_andi := true
    cpuregs_rs1 := wordOfNat 11
    decoded_imm := wordOfNat 7 }

def afterImmediate := nextState immediateInputs initialState
example : BitVector.toNat 32 (afterImmediate .reg_op1) = 11 := by decide
example : BitVector.toNat 32 (afterImmediate .reg_op2) = 7 := by decide

def registerOperands : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    cpuregs_rs1 := wordOfNat 13
    cpuregs_rs2 := wordOfNat 21 }

def afterRegisterOperands := nextState registerOperands initialState
example : BitVector.toNat 32 (afterRegisterOperands .reg_op1) = 13 := by decide
example : BitVector.toNat 32 (afterRegisterOperands .reg_op2) = 21 := by decide
example : shiftAmount afterRegisterOperands = 21 := by decide

def aluCaptureInputs : Inputs :=
  { idleInputs with is_lui_auipc_jal_jalr_addi_add_sub := true }

def afterAluCapture := nextState aluCaptureInputs (stateWith 0 0 5 3 0 0 0)
example : BitVector.toNat 32 (afterAluCapture .alu_out_q) = 8 := by decide

end Silean.Examples.Checks.PicoRVDatapathFlowChecks
