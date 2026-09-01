import Silean.Examples.Fixtures.PicoRVDatapath

namespace Silean.Examples.Checks.PicoRVDatapathArithmeticShiftChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

def shiftLeftInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_sll := true }

def shiftStart := stateWith 0 0 1 0 0 9 0
def shiftAfter1 := nextState shiftLeftInputs shiftStart
def evaluatedShift := cycleContract.evaluate (inputValues shiftLeftInputs) shiftStart

example : evaluatedShift.2 = shiftAfter1 := by rfl
example : BitVector.toNat 32 (evaluatedShift.1 .reg_op1) = 1 := by decide

def arithmeticShiftInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateShift, instr_sra := true }

def arithmeticAfter1 := nextState arithmeticShiftInputs
  (stateWith 0 0 0x80000000 0 0 4 0)

example : BitVector.toNat 32 (arithmeticAfter1 .reg_op1) = 0xf8000000 := by decide
example : shiftAmount arithmeticAfter1 = 0 := by decide

end Silean.Examples.Checks.PicoRVDatapathArithmeticShiftChecks
