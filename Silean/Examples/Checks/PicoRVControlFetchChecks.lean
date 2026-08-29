import Silean.Examples.Checks.PicoRVControlFixtures

namespace Silean.Examples.Checks.PicoRVControlFetchChecks

open Silean
open Silean.Examples.PicoRV.Control
open Silean.Examples.Checks.PicoRVControlFixtures

def resetSource := commandState cpuStateExec true true false false
def resetState := nextState { idleInputs with resetn := false } resetSource

example : phase resetState = cpuStateFetch := by decide
example : (resetState .latched_store : Bool) = false := by rfl
example : (resetState .mem_do_prefetch : Bool) = false := by rfl
example : (resetState .mem_do_rinst : Bool) = false := by rfl

def waitingFetch := nextState idleInputs (stateIn cpuStateFetch)
example : phase waitingFetch = cpuStateFetch := by decide
example : (waitingFetch .mem_do_rinst : Bool) = true := by rfl

def decodedFetch := stateMap.set (stateIn cpuStateFetch) .decoder_trigger true

def jalState := nextState { idleInputs with instr_jal := true } decodedFetch
example : phase jalState = cpuStateFetch := by decide
example : (jalState .latched_branch : Bool) = true := by rfl
example : (jalState .mem_do_rinst : Bool) = true := by rfl

def ordinaryState := nextState idleInputs decodedFetch
example : phase ordinaryState = cpuStateLdRs1 := by decide
example : (ordinaryState .mem_do_prefetch : Bool) = true := by rfl
example : (ordinaryState .mem_do_rinst : Bool) = false := by rfl

def jalrState := nextState { idleInputs with instr_jalr := true } decodedFetch
example : phase jalrState = cpuStateLdRs1 := by decide
example : (jalrState .mem_do_prefetch : Bool) = false := by rfl

end Silean.Examples.Checks.PicoRVControlFetchChecks
