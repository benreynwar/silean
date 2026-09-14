import Silean.Examples.Fixtures.PicoRVDatapath

namespace Silean.Examples.Checks.PicoRVDatapathShiftChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

/-! ## Step-size boundaries

Zero captures the finished result. Positive counts below four consume one bit
per edge; counts of four or more consume four. These first-edge checks make
the important boundary counts explicit without hiding the iterative timing in
a host-language shift operation. -/

def firstLeftStep (amount : Nat) := nextState
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_sll := true }
  (stateWith 0 0 1 0 0 amount 0)

example : BitVector.toNat 32 ((firstLeftStep 0) .reg_out) = 1 := by decide
example : BitVector.toNat 32 ((firstLeftStep 1) .reg_op1) = 2 := by decide
example : shiftAmount (firstLeftStep 1) = 0 := by decide
example : BitVector.toNat 32 ((firstLeftStep 3) .reg_op1) = 2 := by decide
example : shiftAmount (firstLeftStep 3) = 2 := by decide
example : BitVector.toNat 32 ((firstLeftStep 4) .reg_op1) = 16 := by decide
example : shiftAmount (firstLeftStep 4) = 0 := by decide
example : BitVector.toNat 32 ((firstLeftStep 5) .reg_op1) = 16 := by decide
example : shiftAmount (firstLeftStep 5) = 1 := by decide
example : BitVector.toNat 32 ((firstLeftStep 31) .reg_op1) = 16 := by decide
example : shiftAmount (firstLeftStep 31) = 27 := by decide

/-! ## Mode and overlap priority

Logical right fills with zero, while arithmetic right replicates the sign bit.
If malformed decoder inputs assert multiple modes, source ordering is total:
left wins first, then logical right, then arithmetic right. -/

def logicalRightAfter4 := nextState
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_srl := true }
  (stateWith 0 0 0x80000010 0 0 4 0)

def arithmeticRightAfter4 := nextState
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_sra := true }
  (stateWith 0 0 0x80000010 0 0 4 0)

def leftWinsOverlap := nextState
  { idleInputs with
    cpu_state := stateBits cpuStateShift
    instr_sll := true
    instr_srl := true
    instr_sra := true }
  (stateWith 0 0 0x80000010 0 0 4 0)

def logicalWinsRightOverlap := nextState
  { idleInputs with
    cpu_state := stateBits cpuStateShift
    instr_srl := true
    instr_sra := true }
  (stateWith 0 0 0x80000010 0 0 4 0)

example : BitVector.toNat 32 (logicalRightAfter4 .reg_op1) = 0x08000001 := by decide
example : BitVector.toNat 32 (arithmeticRightAfter4 .reg_op1) = 0xf8000001 := by decide
example : BitVector.toNat 32 (leftWinsOverlap .reg_op1) = 0x00000100 := by decide
example : BitVector.toNat 32 (logicalWinsRightOverlap .reg_op1) = 0x08000001 := by decide

/-! ## Multi-edge progression -/

def shiftLeftInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_sll := true }

def shift9Start := stateWith 0 0 1 0 0 9 0
def shift9After1 := nextState shiftLeftInputs shift9Start
def shift9After2 := nextState shiftLeftInputs shift9After1
def shift9After3 := nextState shiftLeftInputs shift9After2
def shift9After4 := nextState shiftLeftInputs shift9After3

example : BitVector.toNat 32 (shift9After1 .reg_op1) = 16 := by decide
example : shiftAmount shift9After1 = 5 := by decide
example : BitVector.toNat 32 (shift9After2 .reg_op1) = 256 := by decide
example : shiftAmount shift9After2 = 1 := by decide
example : BitVector.toNat 32 (shift9After3 .reg_op1) = 512 := by decide
example : shiftAmount shift9After3 = 0 := by decide
example : BitVector.toNat 32 (shift9After4 .reg_out) = 512 := by decide

end Silean.Examples.Checks.PicoRVDatapathShiftChecks
