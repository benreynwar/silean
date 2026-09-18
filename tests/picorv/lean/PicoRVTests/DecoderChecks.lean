import PicoRV.DecoderTheorems
import Silean.FIRRTL

namespace PicoRVTests.DecoderChecks

open PicoRV.Decoder

def addiX1X2Five : Word := wordOfNat 0x00510093

def idleInputs : Inputs where
  resetn := true
  mem_do_rinst := false
  mem_done := false
  mem_rdata_latched := wordOfNat 0
  decoder_trigger := false
  decoder_pseudo_trigger := false
  mem_rdata_q := wordOfNat 0

def captureAddi : Inputs :=
  { idleInputs with
    mem_do_rinst := true
    mem_done := true
    mem_rdata_latched := addiX1X2Five }

def resolveAddi : Inputs :=
  { idleInputs with decoder_trigger := true, mem_rdata_q := addiX1X2Five }

def initialState : stateMap.Values := stateMap.defaultValues
def capturedAddi : stateMap.Values := nextState captureAddi initialState
def resolvedAddi : stateMap.Values := nextState resolveAddi capturedAddi
def summarizedAddi : stateMap.Values := nextState idleInputs resolvedAddi

-- Both stages see the same pre-edge state. The resolve stage therefore still
-- decodes ADDI while the capture stage replaces its opcode class with LUI.
def captureLuiResolveAddi : Inputs :=
  { captureAddi with
    mem_rdata_latched := wordOfNat 0x000000b7
    decoder_trigger := true
    mem_rdata_q := addiX1X2Five }

def simultaneousResult : stateMap.Values :=
  nextState captureLuiResolveAddi capturedAddi

example : (simultaneousResult .instr_lui : Bool) = true := by rfl
example : (simultaneousResult .instr_addi : Bool) = true := by rfl

example : (capturedAddi .is_alu_reg_imm : Bool) = true := by rfl
example : Silean.BitVector.toNat 5 (capturedAddi .decoded_rd) = 1 := by decide
example : Silean.BitVector.toNat 5 (capturedAddi .decoded_rs1) = 2 := by decide
example : (resolvedAddi .instr_addi : Bool) = true := by rfl
example : Silean.BitVector.toNat 32 (resolvedAddi .decoded_imm) = 5 := by decide
example : Silean.BitVector.toNat 32 (immediateI (wordOfNat 0xfff10093)) = 0xffffffff := by decide
example : Silean.BitVector.toNat 32 (immediateU (wordOfNat 0x123450b7)) = 0x12345000 := by decide
example : Silean.BitVector.toNat 32 (immediateB (wordOfNat 0x00000463)) = 8 := by decide
example : Silean.BitVector.toNat 32 (immediateJ (wordOfNat 0x0080006f)) = 8 := by decide
example : Silean.BitVector.toNat 32 (immediateS (wordOfNat 0xfe002e23)) = 0xfffffffc := by decide

-- The source clears this aggregate in the resolve block; the unconditional
-- summary assignment observes `instr_addi` on the following edge.
example : (resolvedAddi .is_lui_auipc_jal_jalr_addi_add_sub : Bool) = false := by rfl
example : (summarizedAddi .is_lui_auipc_jal_jalr_addi_add_sub : Bool) = true := by rfl

def resetState : stateMap.Values :=
  stateMap.set (stateMap.set initialState .instr_lui true) .instr_addi true

example : ((nextState { idleInputs with resetn := false } resetState) .instr_addi : Bool) = false := by
  rfl

-- `instr_lui` is deliberately not reset in the source decoder block.
example : ((nextState { idleInputs with resetn := false } resetState) .instr_lui : Bool) = true := by
  rfl

example : (outputValues resolvedAddi .instr_trap : Bool) = false := by rfl
example : (outputValues initialState .instr_trap : Bool) = true := by rfl
example : (resolvedAddi .instr_addi : Bool) = true := by rfl

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified ports := certified

example : ResolveStage.structuralChildren .instructionMatch =
    InstructionMatch.Structure.moduleStructure := rfl
example : ResolveStage.structuralChildren .immediate = Immediate.moduleStructure := rfl
example : Immediate.moduleStructure.HasNoBlackboxes :=
  Immediate.moduleStructure_hasNoBlackboxes
example : ResolveStage.structuralChildren .instructionSummary =
    InstructionSummary.Structure.moduleStructure := rfl

example : moduleStructure.HasNoBlackboxes := moduleStructure_hasNoBlackboxes

#guard match Silean.FIRRTL.renderClosedCircuit naming with
  | .ok _ => true
  | .error _ => false

end PicoRVTests.DecoderChecks
