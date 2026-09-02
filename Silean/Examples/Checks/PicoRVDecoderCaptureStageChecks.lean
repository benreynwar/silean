import Silean.FIRRTL
import Silean.Examples.PicoRV.Decoder

namespace Silean.Examples.Checks.PicoRVDecoderCaptureStageChecks

open Silean
open Silean.FIRRTL
open Silean.Examples.PicoRV.Decoder.CaptureStage

def emptyState : stateMap.Values := stateMap.defaultValues

def capture (word : Nat) (resetn := true) : Inputs where
  resetn := resetn
  mem_do_rinst := true
  mem_done := true
  mem_rdata_latched := Silean.Examples.PicoRV.Decoder.wordOfNat word

def idle : Inputs where
  resetn := true
  mem_do_rinst := false
  mem_done := false
  mem_rdata_latched := Silean.Examples.PicoRV.Decoder.wordOfNat 0

-- ADDI x1, x2, 5: capture enable, opcode class, and register slices agree.
def addiState := nextState (capture 0x00510093) emptyState
example : (addiState .is_alu_reg_imm : Bool) = true := by rfl
example : BitVector.toNat 5 (addiState .decoded_rd) = 1 := by decide
example : BitVector.toNat 5 (addiState .decoded_rs1) = 2 := by decide

-- JALR is recognized only for opcode 0x67 with funct3 equal to zero.
example : ((nextState (capture 0x000100e7) emptyState) .instr_jalr : Bool) = true := by rfl
example : ((nextState (capture 0x000110e7) emptyState) .instr_jalr : Bool) = false := by rfl

-- JAL +8 exercises the non-contiguous J-immediate combiner.
example : BitVector.toNat 32
    ((nextState (capture 0x0080006f) emptyState) .decoded_imm_j) = 8 := by decide

-- Reset wins over a simultaneous branch capture, while the shared capture
-- still updates the fields that PicoRV32 deliberately does not reset.
def resetBranch := nextState (capture 0x00208463 false) emptyState
example : (resetBranch .is_beq_bne_blt_bge_bltu_bgeu : Bool) = false := by rfl
example : BitVector.toNat 5 (resetBranch .decoded_rd) = 8 := by decide

-- With capture disabled, all capture-stage state is held.
example : nextState idle addiState = addiState := by
  funext register
  cases register <;> rfl

noncomputable example : Contracts.Cycle.ModuleCycleCertified ports := certified

example : moduleStructure.HasNoBlackboxes := by
  native_decide

noncomputable example : RenderResult String :=
  renderClosedCircuit Naming.naming

#guard renderModuleKey Naming.naming.key = "picorv32_decoder_capture_structural"
#guard Naming.ports.inputs.name .mem_rdata_latched = "mem_rdata_latched"
#guard Naming.ports.outputs.name .decoded_imm_j = "decoded_imm_j"

-- Only this child changed in the certified parent decoder.
example : Silean.Examples.PicoRV.Decoder.structuralChildren .capture = moduleStructure := rfl
example : Silean.Examples.PicoRV.Decoder.structuralChildren .resolve =
    Silean.Examples.PicoRV.Decoder.ResolveStage.cycleContract.blackboxStructure := rfl

end Silean.Examples.Checks.PicoRVDecoderCaptureStageChecks
