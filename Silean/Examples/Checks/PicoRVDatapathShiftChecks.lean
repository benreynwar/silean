import Silean.Examples.Fixtures.PicoRVDatapath

namespace Silean.Examples.Checks.PicoRVDatapathShiftChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

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
