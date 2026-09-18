import PicoRV.MemoryTheorems
import Silean.FIRRTL

namespace PicoRVTests.MemoryChecks

open Silean
open Silean.FIRRTL
open PicoRV.Memory

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

/-! ## Instruction request lifecycle

The look-ahead request is visible before the edge that records the ordinary
request. Once recorded, every request field remains stable during a stall.
The response is captured and completion is reported on the transfer cycle. -/

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
example : Silean.BitVector.toNat 32 (instructionRequest .mem_addr) = 0x1000 := by decide
example : Silean.BitVector.toNat 4 (instructionRequest .mem_wstrb) = 0 := by decide

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
example : Silean.BitVector.toNat 32 (afterInstruction .mem_rdata_q) = 0x00510093 := by decide

/-! ## Read and write lane formatting -/

def byteStore : Inputs :=
  { idleInputs with
    mem_do_wdata := true
    reg_op1 := wordOfNat 0x2002
    reg_op2 := wordOfNat 0xaa
    mem_wordsize := stateOfNat 2 }

def byteStoreRequest : stateMap.Values := nextState byteStore initialState

example : phase byteStoreRequest = .writeRequest := by rfl
example : (byteStoreRequest .mem_instr : Bool) = false := by rfl
example : Silean.BitVector.toNat 32 (byteStoreRequest .mem_addr) = 0x2000 := by decide
example : Silean.BitVector.toNat 32 (byteStoreRequest .mem_wdata) = 0xaaaaaaaa := by decide
example : Silean.BitVector.toNat 4 (byteStoreRequest .mem_wstrb) = 0x4 := by decide

def halfAccess : Inputs :=
  { idleInputs with
    reg_op1 := wordOfNat 0x2002
    reg_op2 := wordOfNat 0x1234
    mem_wordsize := stateOfNat 1
    mem_rdata := wordOfNat 0xabcd5678 }

example : Silean.BitVector.toNat 32 (formattedWriteData halfAccess) = 0x12341234 := by decide
example : Silean.BitVector.toNat 4 (formattedWriteMask halfAccess) = 0xc := by decide
example : Silean.BitVector.toNat 32 (formattedReadData halfAccess) = 0xabcd := by decide
example : Silean.BitVector.toNat 32
    (formattedReadData { halfAccess with mem_wordsize := stateOfNat 2 }) = 0xcd := by decide

example : Silean.BitVector.toNat 4
    (formattedWriteMask { halfAccess with reg_op1 := wordOfNat 0x2000 }) = 0x3 := by decide
example : Silean.BitVector.toNat 32
    (formattedReadData { halfAccess with reg_op1 := wordOfNat 0x2000 }) = 0x5678 := by decide

def byteLane (lane : Nat) : Inputs :=
  { idleInputs with
    reg_op1 := wordOfNat (0x2000 + lane)
    reg_op2 := wordOfNat 0x5a
    mem_wordsize := stateOfNat 2
    mem_rdata := wordOfNat 0x44332211 }

example : Silean.BitVector.toNat 4 (formattedWriteMask (byteLane 0)) = 0x1 := by decide
example : Silean.BitVector.toNat 4 (formattedWriteMask (byteLane 1)) = 0x2 := by decide
example : Silean.BitVector.toNat 4 (formattedWriteMask (byteLane 2)) = 0x4 := by decide
example : Silean.BitVector.toNat 4 (formattedWriteMask (byteLane 3)) = 0x8 := by decide
example : Silean.BitVector.toNat 32 (formattedReadData (byteLane 0)) = 0x11 := by decide
example : Silean.BitVector.toNat 32 (formattedReadData (byteLane 1)) = 0x22 := by decide
example : Silean.BitVector.toNat 32 (formattedReadData (byteLane 2)) = 0x33 := by decide
example : Silean.BitVector.toNat 32 (formattedReadData (byteLane 3)) = 0x44 := by decide

def totalizedWordSize : Inputs :=
  { idleInputs with
    reg_op1 := wordOfNat 0x2003
    reg_op2 := wordOfNat 0x12345678
    mem_wordsize := stateOfNat 3
    mem_rdata := wordOfNat 0x89abcdef }

/-! Encoding 3 is unreachable under `InputsWellFormed`. The contract makes
the source's `full_case` don't-care path total by treating it as a word. -/
example : formattedWriteData totalizedWordSize = totalizedWordSize.reg_op2 := by rfl
example : Silean.BitVector.toNat 4 (formattedWriteMask totalizedWordSize) = 0xf := by decide
example : formattedReadData totalizedWordSize = totalizedWordSize.mem_rdata := by rfl

/-! ## Delayed prefetch completion -/

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

/-! ## Reset and trap edge priority

Ordinary outputs describe the pre-edge state. The values below describe the
state after the edge. Response capture is in a separate source process, so it
still occurs when reset or trap is asserted on the transfer edge. -/

def resetRequest : stateMap.Values :=
  nextState { stalledInstruction with resetn := false } instructionRequest

example : phase resetRequest = .idle := by rfl
example : (resetRequest .mem_valid : Bool) = false := by rfl

def resetTransfer : stateMap.Values :=
  nextState { completedInstruction with resetn := false } instructionRequest

example : phase resetTransfer = .idle := by rfl
example : (resetTransfer .mem_valid : Bool) = false := by rfl
example : Silean.BitVector.toNat 32 (resetTransfer .mem_rdata_q) = 0x00510093 := by decide

def trapTransfer : stateMap.Values :=
  nextState { completedInstruction with trap := true } instructionRequest

/-! Trap does not reset `mem_state`; readiness only clears `mem_valid`. -/
example : phase trapTransfer = .readRequest := by rfl
example : (trapTransfer .mem_valid : Bool) = false := by rfl
example : Silean.BitVector.toNat 32 (trapTransfer .mem_rdata_q) = 0x00510093 := by decide

def trapStall : stateMap.Values :=
  nextState { stalledInstruction with trap := true } instructionRequest

example : request? trapStall = request? instructionRequest := by rfl

/-! ## Source priority for malformed commands

Control excludes this overlap. It remains useful to check because universal
certification covers every input: the later write-state assignments win, while
the earlier read-side address selection and strobe clearing remain visible. -/

def overlappingReadWrite : Inputs :=
  { idleInputs with
    mem_do_rinst := true
    mem_do_wdata := true
    next_pc := wordOfNat 0x4003
    reg_op1 := wordOfNat 0x5002
    reg_op2 := wordOfNat 0xaa
    mem_wordsize := stateOfNat 2 }

def overlappingRequest : stateMap.Values :=
  nextState overlappingReadWrite initialState

example : phase overlappingRequest = .writeRequest := by rfl
example : (overlappingRequest .mem_instr : Bool) = false := by rfl
example : Silean.BitVector.toNat 32 (overlappingRequest .mem_addr) = 0x4000 := by decide
example : Silean.BitVector.toNat 32 (overlappingRequest .mem_wdata) = 0xaaaaaaaa := by decide
example : Silean.BitVector.toNat 4 (overlappingRequest .mem_wstrb) = 0 := by decide

/-! ## Concrete structural boundary

The witnesses below connect every executable contract example above to the
stateful aggregate-register hierarchy. They also ensure the standalone memory
can be solved uniquely and emitted without any hidden behavioral leaf. -/

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified ports := certified

example : moduleStructure.HasNoBlackboxes := moduleStructure_hasNoBlackboxes

example : moduleStructure.HasAtMostOneSolution :=
  certified.certification.structuralResultUnique

noncomputable example : RenderResult String := renderClosedCircuit naming

#guard match renderClosedCircuit naming with
  | .ok _ => true
  | .error _ => false

#guard renderModuleKey naming.key = "PicoRVMemory"

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule naming with
  | .error _ => false
  | .ok text =>
      ["public module PicoRVMemory",
       "inst storage",
       "inst lookahead",
       "inst readFormatting",
       "inst response",
       "inst next",
       "output mem_valid : UInt<1>",
       "output mem_addr : UInt<1>[32]"].all (contains text)

end PicoRVTests.MemoryChecks
