import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatch
import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummary
import Silean.Examples.PicoRV.Decoder.DecoderResolveStage

namespace Silean.Examples.Checks.PicoRVDecoderResolveChildrenChecks

open Silean
open Silean.Examples.PicoRV.Decoder

namespace Match

open InstructionMatch

def immediateClass (word : Nat) : Inputs where
  word := wordOfNat word
  instr_jalr := false
  is_beq_bne_blt_bge_bltu_bgeu := false
  is_lb_lh_lw_lbu_lhu := false
  is_sb_sh_sw := false
  is_alu_reg_imm := true
  is_alu_reg_reg := false

def bit (inputs : Inputs) (output : Output) : Bool :=
  cast (congrArg SignalType.Denote (output_signalType output))
    (outputValues inputs output)

-- ADDI x1, x2, 5 is an ordinary immediate operation and belongs to the
-- non-shift immediate summary class.
example : bit (immediateClass 0x00510093) .instr_addi = true := by decide
example : bit (immediateClass 0x00510093) .instr_slli = false := by decide
example : bit (immediateClass 0x00510093)
    .is_jalr_addi_slti_sltiu_xori_ori_andi = true := by decide

-- SRAI requires both funct3 = 5 and funct7 = 0x20.
example : bit (immediateClass 0x40315093) .instr_srai = true := by decide
example : bit (immediateClass 0x00315093) .instr_srai = false := by decide
example : bit (immediateClass 0x40315093) .is_slli_srli_srai = true := by decide

def registerClass (word : Nat) : Inputs :=
  { immediateClass word with is_alu_reg_imm := false, is_alu_reg_reg := true }

-- SUB x3, x1, x2 exercises the register funct7 distinction.
example : bit (registerClass 0x402081b3) .instr_sub = true := by decide
example : bit (registerClass 0x002081b3) .instr_sub = false := by decide

-- Fence matching follows opcode/funct3 directly and is not gated by a broad
-- captured opcode class.
example : bit (immediateClass 0x0000000f) .instr_fence = true := by decide

-- ECALL and EBREAK share the source predicate; disabled counter and IRQ
-- instructions are intentionally absent from this configured boundary.
example : bit (immediateClass 0x00000073) .instr_ecall_ebreak = true := by decide
example : bit (immediateClass 0x00100073) .instr_ecall_ebreak = true := by decide

example (input : Input) : input ∈ outputRule.readsInputs.labels := outputRule_reads input
example (output : Output) : output ∈ outputRule.writesOutputs.labels := outputRule_writes output
example : cycleContract.state = emptySignalMap := rfl

end Match

namespace ImmediateChecks

open Immediate

def base (word : Nat) : Inputs where
  word := wordOfNat word
  decoded_imm_j := wordOfNat 0
  instr_jal := false
  instr_lui := false
  instr_auipc := false
  instr_jalr := false
  is_lb_lh_lw_lbu_lhu := false
  is_alu_reg_imm := false
  is_beq_bne_blt_bge_bltu_bgeu := false
  is_sb_sh_sw := false

def evaluatedNat (inputs : Inputs) : Option Nat :=
  (evaluate inputs).map (BitVector.toNat 32)

def valid (inputs : Inputs) : Bool := outputValues inputs .valid

example : evaluatedNat { base 0x12345037 with instr_lui := true } =
    some 0x12345000 := by decide
example : evaluatedNat { base 0xfff10093 with is_alu_reg_imm := true } =
    some 0xffffffff := by decide
example : evaluatedNat { base 0x00208463 with is_beq_bne_blt_bge_bltu_bgeu := true } =
    some 8 := by decide
example : evaluatedNat { base 0x0020a423 with is_sb_sh_sw := true } =
    some 8 := by decide

-- The contract represents the Verilog don't-care branch as absence. The
-- resolve parent can therefore hold its registered immediate.
example : evaluate (base 0) = none := by decide
example : valid (base 0) = false := by decide

-- Source case order gives JAL priority if inconsistent selectors overlap.
def overlapping : Inputs where
  word := wordOfNat 0x12345037
  decoded_imm_j := wordOfNat 12
  instr_jal := true
  instr_lui := true
  instr_auipc := false
  instr_jalr := false
  is_lb_lh_lw_lbu_lhu := false
  is_alu_reg_imm := false
  is_beq_bne_blt_bge_bltu_bgeu := false
  is_sb_sh_sw := false
example : evaluatedNat overlapping = some 12 := by decide

example (input : Input) : input ∈ outputRule.readsInputs.labels := outputRule_reads input
example (output : Output) : output ∈ outputRule.writesOutputs.labels := outputRule_writes output
example : cycleContract.state = emptySignalMap := rfl

end ImmediateChecks

namespace SummaryChecks

open InstructionSummary

def emptyInputs : inputMap.Values := inputMap.defaultValues
def addiInputs : inputMap.Values := inputMap.set emptyInputs .instr_addi true
def branchClassInputs : inputMap.Values :=
  inputMap.set emptyInputs .is_beq_bne_blt_bge_bltu_bgeu true
def ecallInputs : inputMap.Values :=
  inputMap.set emptyInputs .instr_ecall_ebreak true

def bit (inputs : Inputs) (output : Output) : Bool :=
  cast (congrArg SignalType.Denote (output_signalType output))
    (outputValues inputs output)

-- Exact current flags make an instruction recognized and feed the summaries.
example : bit (valuesOf addiInputs) .instr_trap = false := by decide
example : bit (valuesOf addiInputs)
    .is_lui_auipc_jal_jalr_addi_add_sub = true := by decide

-- With no current instruction flag the configured illegal-instruction output
-- is asserted.
example : bit (valuesOf emptyInputs) .instr_trap = true := by decide

-- The broad branch class contributes to the pre-edge compare summary but is
-- not itself one of the exact instruction flags recognized by instr_trap.
example : bit (valuesOf branchClassInputs) .is_compare = true := by decide
example : bit (valuesOf branchClassInputs) .instr_trap = true := by decide

-- PicoRV32 classifies ECALL/EBREAK separately rather than as an unknown
-- instruction, so the continuous illegal-instruction result is low.
example : bit (valuesOf ecallInputs) .instr_trap = false := by decide

example (input : Input) :
    input ∈ trapOutputRule.readsInputs.labels ↔
      input ≠ .is_beq_bne_blt_bge_bltu_bgeu :=
  trapOutputRule_reads input
example (input : Input) : input ∈ summariesOutputRule.readsInputs.labels :=
  summariesOutputRule_reads input
example (output : Output) :
    output ∈ trapOutputRule.writesOutputs.labels ↔ output = .instr_trap :=
  trapOutputRule_writes output
example (output : Output) :
    output ∈ summariesOutputRule.writesOutputs.labels ↔ output ≠ .instr_trap :=
  summariesOutputRule_writes output
example : cycleContract.state = emptySignalMap := rfl

end SummaryChecks

namespace ExistingResolveContract

def ecallInputs : ResolveStage.Inputs where
  resetn := true
  decoder_trigger := true
  decoder_pseudo_trigger := false
  mem_rdata_q := wordOfNat 0x00000073
  instr_lui := false
  instr_auipc := false
  instr_jal := false
  instr_jalr := false
  decoded_imm_j := wordOfNat 0
  is_beq_bne_blt_bge_bltu_bgeu := false
  is_lb_lh_lw_lbu_lhu := false
  is_sb_sh_sw := false
  is_alu_reg_imm := false
  is_alu_reg_reg := false

def ecallState : ResolveStage.stateMap.Values :=
  ResolveStage.nextState ecallInputs ResolveStage.stateMap.defaultValues

def ecallTrap : Bool := ResolveStage.outputValues ecallInputs ecallState .instr_trap

-- The previously omitted private predicate is now retained by the existing
-- resolve contract, keeping its recognized-instruction view aligned with the
-- configured Verilog and with the new child contracts.
example : (ecallState .instr_ecall_ebreak : Bool) = true := by rfl
example : ecallTrap = false := by rfl

end ExistingResolveContract

end Silean.Examples.Checks.PicoRVDecoderResolveChildrenChecks
