import Silean.Examples.PicoRV.Memory

namespace Silean.Examples.Checks.PicoRVMemoryChecks

open Silean.Examples.PicoRV.Memory

def idleInputs : Inputs where
  resetn := true
  trap := false
  mem_do_prefetch := false
  mem_do_rinst := false
  mem_do_rdata := false
  mem_do_wdata := false
  next_pc := wordOfNat 0
  reg_op1 := wordOfNat 0
  reg_op2 := wordOfNat 0
  mem_wordsize := stateOfNat 0
  mem_ready := false
  mem_rdata := wordOfNat 0

def initialState : stateMap.Values := stateMap.defaultValues

def instructionStart : Inputs :=
  { idleInputs with mem_do_rinst := true, next_pc := wordOfNat 0x1003 }

def instructionRequest : stateMap.Values := nextState instructionStart initialState

def evaluatedInstructionStart :=
  cycleContract.evaluate (inputValues instructionStart) initialState

example : phase instructionRequest = .readRequest := by rfl
example : evaluatedInstructionStart.2 = instructionRequest := by rfl
example : (evaluatedInstructionStart.1 .mem_la_read : Bool) = true := by rfl
example : (evaluatedInstructionStart.1 .mem_valid : Bool) = false := by rfl
example : (instructionRequest .mem_valid : Bool) = true := by rfl
example : (instructionRequest .mem_instr : Bool) = true := by rfl
example : BitVector.toNat 32 (instructionRequest .mem_addr) = 0x1000 := by decide
example : BitVector.toNat 4 (instructionRequest .mem_wstrb) = 0 := by decide

def stalledInstruction : Inputs :=
  { instructionStart with mem_ready := false }

example : request? (nextState stalledInstruction instructionRequest) =
    request? instructionRequest := by rfl
example : memDone stalledInstruction instructionRequest = false := by rfl

def completedInstruction : Inputs :=
  { instructionStart with mem_ready := true, mem_rdata := wordOfNat 0x00510093 }

def afterInstruction : stateMap.Values := nextState completedInstruction instructionRequest

example : memDone completedInstruction instructionRequest = true := by rfl
example : phase afterInstruction = .idle := by rfl
example : (afterInstruction .mem_valid : Bool) = false := by rfl
example : BitVector.toNat 32 (afterInstruction .mem_rdata_q) = 0x00510093 := by decide

def byteStore : Inputs :=
  { idleInputs with
    mem_do_wdata := true
    reg_op1 := wordOfNat 0x2002
    reg_op2 := wordOfNat 0xaa
    mem_wordsize := stateOfNat 2 }

def byteStoreRequest : stateMap.Values := nextState byteStore initialState

example : phase byteStoreRequest = .writeRequest := by rfl
example : (byteStoreRequest .mem_instr : Bool) = false := by rfl
example : BitVector.toNat 32 (byteStoreRequest .mem_addr) = 0x2000 := by decide
example : BitVector.toNat 32 (byteStoreRequest .mem_wdata) = 0xaaaaaaaa := by decide
example : BitVector.toNat 4 (byteStoreRequest .mem_wstrb) = 0x4 := by decide

def halfAccess : Inputs :=
  { idleInputs with
    reg_op1 := wordOfNat 0x2002
    reg_op2 := wordOfNat 0x1234
    mem_wordsize := stateOfNat 1
    mem_rdata := wordOfNat 0xabcd5678 }

example : BitVector.toNat 32 (formattedWriteData halfAccess) = 0x12341234 := by decide
example : BitVector.toNat 4 (formattedWriteMask halfAccess) = 0xc := by decide
example : BitVector.toNat 32 (formattedReadData halfAccess) = 0xabcd := by decide
example : BitVector.toNat 32
    (formattedReadData { halfAccess with mem_wordsize := stateOfNat 2 }) = 0xcd := by decide

def prefetchStart : Inputs :=
  { idleInputs with mem_do_prefetch := true, next_pc := wordOfNat 0x3000 }

def prefetchRequest : stateMap.Values := nextState prefetchStart initialState

def prefetchTransfer : Inputs :=
  { prefetchStart with mem_ready := true, mem_rdata := wordOfNat 0xdeadbeef }

def prefetchedState : stateMap.Values := nextState prefetchTransfer prefetchRequest

example : memDone prefetchTransfer prefetchRequest = false := by rfl
example : phase prefetchedState = .prefetched := by rfl

def consumePrefetch : Inputs := { idleInputs with mem_do_rinst := true }
example : memXfer consumePrefetch prefetchedState = false := by rfl
example : memDone consumePrefetch prefetchedState = true := by rfl
example : phase (nextState consumePrefetch prefetchedState) = .idle := by rfl

def resetRequest : stateMap.Values :=
  nextState { stalledInstruction with resetn := false } instructionRequest

example : phase resetRequest = .idle := by rfl
example : (resetRequest .mem_valid : Bool) = false := by rfl

end Silean.Examples.Checks.PicoRVMemoryChecks
