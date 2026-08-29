import Silean.Examples.Checks.PicoRVDatapathFixtures

namespace Silean.Examples.Checks.PicoRVDatapathOutputChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Checks.PicoRVDatapathFixtures

def branchInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateFetch
    latched_store := true
    latched_stalu := true
    latched_branch := true }

def branchState := stateWith 0x1000 0x2000 7 9 0x3003 0 0x4003
def evaluatedBranch := cycleContract.evaluate (inputValues branchInputs) branchState

example : BitVector.toNat 32 (evaluatedBranch.1 .reg_pc) = 0x1000 := by decide
example : BitVector.toNat 32 (evaluatedBranch.1 .reg_op1) = 7 := by decide
example : BitVector.toNat 32 (evaluatedBranch.1 .next_pc) = 0x3002 := by decide
example : BitVector.toNat 32 (evaluatedBranch.1 .cpuregs_wrdata) = 0x1004 := by decide

def equalInputs : Inputs :=
  { idleInputs with instr_beq := true }

def evaluatedEqual := cycleContract.evaluate (inputValues equalInputs)
  (stateWith 0 0 23 23 0 0 0)

example : (evaluatedEqual.1 .alu_out_0 : Bool) = true := by rfl

end Silean.Examples.Checks.PicoRVDatapathOutputChecks
