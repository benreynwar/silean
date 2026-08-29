import Silean.Examples.Checks.PicoRVControlFixtures

namespace Silean.Examples.Checks.PicoRVControlMemoryChecks

open Silean
open Silean.Examples.PicoRV.Control
open Silean.Examples.Checks.PicoRVControlFixtures

def byteLoadStart := nextState
  { idleInputs with instr_lb := true, is_lbu_lhu_lw := false }
  (stateIn cpuStateLdmem)

example : wordSize byteLoadStart = 2 := by decide
example : (byteLoadStart .latched_is_lb : Bool) = true := by rfl
example : (byteLoadStart .mem_do_rdata : Bool) = true := by rfl

def loadComplete := nextState { idleInputs with mem_done := true }
  (commandState cpuStateLdmem false false true false)

example : phase loadComplete = cpuStateFetch := by decide
example : (loadComplete .decoder_trigger : Bool) = true := by rfl
example : (loadComplete .decoder_pseudo_trigger : Bool) = true := by rfl
example : (loadComplete .mem_do_rdata : Bool) = false := by rfl

def halfStoreStart := nextState { idleInputs with instr_sh := true }
  (stateIn cpuStateStmem)

example : wordSize halfStoreStart = 1 := by decide
example : (halfStoreStart .mem_do_wdata : Bool) = true := by rfl

def storeComplete := nextState { idleInputs with mem_done := true }
  (commandState cpuStateStmem false false false true)

example : phase storeComplete = cpuStateFetch := by decide
example : (storeComplete .decoder_pseudo_trigger : Bool) = true := by rfl
example : (storeComplete .mem_do_wdata : Bool) = false := by rfl

def dataMisalignedState :=
  let state := stateMap.set (commandState cpuStateLdmem false false true false)
    .mem_wordsize (twoBitsOfNat 0)
  nextState { idleInputs with reg_op1 := wordOfNat 2 } state

example : phase dataMisalignedState = cpuStateTrap := by decide

def instructionMisalignedState := nextState
  { idleInputs with reg_pc := wordOfNat 2 }
  (commandState cpuStateFetch false true false false)

example : phase instructionMisalignedState = cpuStateTrap := by decide

end Silean.Examples.Checks.PicoRVControlMemoryChecks
