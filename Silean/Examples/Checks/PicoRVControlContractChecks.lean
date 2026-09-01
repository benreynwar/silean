import Silean.Examples.Fixtures.PicoRVControl

namespace Silean.Examples.Checks.PicoRVControlContractChecks

open Silean
open Silean.Examples.PicoRV.Control
open Silean.Examples.Fixtures.PicoRVControl

def writebackState :=
  let state := stateMap.set (stateIn cpuStateFetch) .latched_store true
  stateMap.set state .latched_rd (fiveBitsOfNat 3)

def evaluatedWriteback := cycleContract.evaluate (inputValues idleInputs) writebackState

example : (evaluatedWriteback.1 .cpuregs_write : Bool) = true := by rfl
example : BitVector.toNat 5 (evaluatedWriteback.1 .latched_rd) = 3 := by decide
example : evaluatedWriteback.2 = nextState idleInputs writebackState := by rfl

def instructionCommands := commandState cpuStateExec true true false false
example : (commands instructionCommands).wellFormed = true := by rfl
example : Silean.Examples.PicoRV.Memory.CommandsWellFormed
    (memoryInputs idleInputs instructionCommands) := by
  apply (commands_wellFormed_iff_memory idleInputs instructionCommands).mp
  rfl

def invalidDataOverlap := commandState cpuStateLdmem true false true false
example : (commands invalidDataOverlap).wellFormed = false := by rfl

def resetCommands := nextState { idleInputs with resetn := false }
  (commandState cpuStateExec true true false false)
example : (commands resetCommands).wellFormed = true := by rfl

def promotedPrefetch := nextState
  { idleInputs with is_jalr_addi_slti_sltiu_xori_ori_andi := true }
  (commandState cpuStateLdRs1 true false false false)
example : (commands promotedPrefetch).wellFormed = true := by rfl
example : (promotedPrefetch .mem_do_prefetch : Bool) = true := by rfl
example : (promotedPrefetch .mem_do_rinst : Bool) = true := by rfl

end Silean.Examples.Checks.PicoRVControlContractChecks
