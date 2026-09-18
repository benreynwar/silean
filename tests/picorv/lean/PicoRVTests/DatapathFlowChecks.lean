import PicoRVTests.Fixtures.PicoRVDatapath

namespace PicoRVTests.DatapathFlowChecks

open Silean
open PicoRV.Datapath
open PicoRVTests.Fixtures.PicoRVDatapath

def resetState := nextState
  { idleInputs with
    resetn := false
    is_lui_auipc_jal_jalr_addi_add_sub := true }
  (stateWith 0x1000 0x2000 3 4 5 6 7)

example : Silean.BitVector.toNat 32 (resetState .reg_pc) = 0 := by decide
example : Silean.BitVector.toNat 32 (resetState .reg_next_pc) = 0 := by decide
example : Silean.BitVector.toNat 32 (resetState .reg_op1) = 3 := by decide
example : Silean.BitVector.toNat 32 (resetState .alu_out_q) = 7 := by decide

def sequentialFetchInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateFetch, decoder_trigger := true }

def afterSequentialFetch := nextState sequentialFetchInputs
  (stateWith 0x1000 0x2000 0 0 0 0 0)

example : Silean.BitVector.toNat 32 (afterSequentialFetch .reg_pc) = 0x2000 := by decide
example : Silean.BitVector.toNat 32 (afterSequentialFetch .reg_next_pc) = 0x2004 := by decide

def jalFetchInputs : Inputs :=
  { sequentialFetchInputs with instr_jal := true, decoded_imm_j := wordOfNat 0x40 }

def afterJalFetch := nextState jalFetchInputs
  (stateWith 0x1000 0x2000 0 0 0 0 0)

example : Silean.BitVector.toNat 32 (afterJalFetch .reg_pc) = 0x2000 := by decide
example : Silean.BitVector.toNat 32 (afterJalFetch .reg_next_pc) = 0x2040 := by decide

/-! A decoded branch that was not taken has `latched_branch` set but not
`latched_store`. It therefore follows the ordinary sequential PC path. -/

def untakenBranchInputs : Inputs :=
  { sequentialFetchInputs with latched_branch := true, latched_store := false }

def afterUntakenBranch := nextState untakenBranchInputs
  (stateWith 0x1000 0x2000 0 0 0x3003 0 0x4003)

example : Silean.BitVector.toNat 32 (afterUntakenBranch .reg_pc) = 0x2000 := by decide
example : Silean.BitVector.toNat 32 (afterUntakenBranch .reg_next_pc) = 0x2004 := by decide

/-! A taken control transfer clears target bit zero. The combinational
`next_pc` look-ahead uses `reg_out`; with `latched_stalu` set, the following
fetch edge commits the captured ALU target from `alu_out_q`, as JALR does.
Branch/JALR writeback supplies the pre-edge PC plus four. -/

def branchFetchInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateFetch
    latched_store := true
    latched_stalu := true
    latched_branch := true }

def branchState := stateWith 0x1000 0x2000 0 0 0x3003 0 0x4003
def afterBranchFetch := nextState branchFetchInputs branchState

example : Silean.BitVector.toNat 32 (afterBranchFetch .reg_pc) = 0x4002 := by decide
example : Silean.BitVector.toNat 32 (nextPcOutput branchFetchInputs branchState) = 0x3002 := by decide
example : Silean.BitVector.toNat 32 (writebackData branchFetchInputs branchState) = 0x1004 := by decide

def luiInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    is_lui_auipc_jal := true
    instr_lui := true
    decoded_imm := wordOfNat 0x12345000 }

def afterLui := nextState luiInputs (stateWith 0x1000 0 0 0 0 0 0)

example : Silean.BitVector.toNat 32 (afterLui .reg_op1) = 0 := by decide
example : Silean.BitVector.toNat 32 (afterLui .reg_op2) = 0x12345000 := by decide

def immediateInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    is_jalr_addi_slti_sltiu_xori_ori_andi := true
    cpuregs_rs1 := wordOfNat 11
    decoded_imm := wordOfNat 7 }

def afterImmediate := nextState immediateInputs initialState
example : Silean.BitVector.toNat 32 (afterImmediate .reg_op1) = 11 := by decide
example : Silean.BitVector.toNat 32 (afterImmediate .reg_op2) = 7 := by decide

def registerOperands : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    cpuregs_rs1 := wordOfNat 13
    cpuregs_rs2 := wordOfNat 21 }

def afterRegisterOperands := nextState registerOperands initialState
example : Silean.BitVector.toNat 32 (afterRegisterOperands .reg_op1) = 13 := by decide
example : Silean.BitVector.toNat 32 (afterRegisterOperands .reg_op2) = 21 := by decide
example : shiftAmount afterRegisterOperands = 21 := by decide

/-! Loads capture only their first-register base in `ld_rs1`; the immediate
is added later when the memory phase starts. Existing `reg_op2` and `reg_sh`
values are deliberately retained. -/

def loadBaseInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    is_lb_lh_lw_lbu_lhu := true
    cpuregs_rs1 := wordOfNat 0x1200 }

def afterLoadBase := nextState loadBaseInputs (stateWith 0 0 3 17 0 9 0)

example : Silean.BitVector.toNat 32 (afterLoadBase .reg_op1) = 0x1200 := by decide
example : Silean.BitVector.toNat 32 (afterLoadBase .reg_op2) = 17 := by decide
example : shiftAmount afterLoadBase = 9 := by decide

/-! An illegal instruction has first priority in the source `ld_rs1` case,
even when a broad opcode-class selector is also true. No operand capture is
performed on that edge. -/

def illegalLoadInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdRs1
    instr_trap := true
    is_lb_lh_lw_lbu_lhu := true
    cpuregs_rs1 := wordOfNat 99 }

def afterIllegalLoad := nextState illegalLoadInputs
  (stateWith 0 0 13 17 0 0 0)

example : Silean.BitVector.toNat 32 (afterIllegalLoad .reg_op1) = 13 := by decide
example : Silean.BitVector.toNat 32 (afterIllegalLoad .reg_op2) = 17 := by decide

/-! `instr_trap` precedes every broad operand-selector branch. These checks
cover the remaining LUI/AUIPC/JAL, immediate-shift, immediate-ALU, and ordinary
fallback paths: none may capture operands for an illegal instruction. -/

def trappedState := stateWith 0x1000 0 13 17 0 9 0

def trappedOperands (inputs : Inputs) := nextState
  { inputs with cpu_state := stateBits cpuStateLdRs1, instr_trap := true }
  trappedState

def trappedLui := trappedOperands
  { idleInputs with
    is_lui_auipc_jal := true
    instr_lui := true
    decoded_imm := wordOfNat 0x12345000 }

def trappedImmediateShift := trappedOperands
  { idleInputs with
    is_slli_srli_srai := true
    cpuregs_rs1 := wordOfNat 99
    decoded_rs2 := fiveBitsOfNat 4 }

def trappedImmediateAlu := trappedOperands
  { idleInputs with
    is_jalr_addi_slti_sltiu_xori_ori_andi := true
    cpuregs_rs1 := wordOfNat 99
    decoded_imm := wordOfNat 7 }

def trappedFallback := trappedOperands
  { idleInputs with cpuregs_rs1 := wordOfNat 99, cpuregs_rs2 := wordOfNat 101 }

example : Silean.BitVector.toNat 32 (trappedLui .reg_op1) = 13 := by decide
example : Silean.BitVector.toNat 32 (trappedLui .reg_op2) = 17 := by decide
example : Silean.BitVector.toNat 32 (trappedImmediateShift .reg_op1) = 13 := by decide
example : shiftAmount trappedImmediateShift = 9 := by decide
example : Silean.BitVector.toNat 32 (trappedImmediateAlu .reg_op1) = 13 := by decide
example : Silean.BitVector.toNat 32 (trappedImmediateAlu .reg_op2) = 17 := by decide
example : Silean.BitVector.toNat 32 (trappedFallback .reg_op1) = 13 := by decide
example : Silean.BitVector.toNat 32 (trappedFallback .reg_op2) = 17 := by decide

def aluCaptureInputs : Inputs :=
  { idleInputs with is_lui_auipc_jal_jalr_addi_add_sub := true }

def afterAluCapture := nextState aluCaptureInputs (stateWith 0 0 5 3 0 0 0)
example : Silean.BitVector.toNat 32 (afterAluCapture .alu_out_q) = 8 := by decide

end PicoRVTests.DatapathFlowChecks
