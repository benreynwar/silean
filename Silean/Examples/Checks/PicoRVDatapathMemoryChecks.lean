import Silean.Examples.Fixtures.PicoRVDatapath

namespace Silean.Examples.Checks.PicoRVDatapathMemoryChecks

open Silean
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

def startLoadInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateLdmem, decoded_imm := wordOfNat 12 }

def loadAddressState := nextState startLoadInputs (stateWith 0 0 0x1000 0 0 0 0)
example : BitVector.toNat 32 (loadAddressState .reg_op1) = 0x100c := by decide

def startStoreInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateStmem, decoded_imm := wordOfNat 20 }

def storeAddressState := nextState startStoreInputs (stateWith 0 0 0x2000 0 0 0 0)
example : BitVector.toNat 32 (storeAddressState .reg_op1) = 0x2014 := by decide

def finishSignedByteLoad : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdmem
    mem_do_rdata := true
    mem_done := true
    latched_is_lb := true
    mem_rdata_word := wordOfNat 0x80 }

def loadedByte := nextState finishSignedByteLoad initialState
example : BitVector.toNat 32 (loadedByte .reg_out) = 0xffffff80 := by decide

def finishSignedHalfLoad : Inputs :=
  { finishSignedByteLoad with
    latched_is_lb := false
    latched_is_lh := true
    mem_rdata_word := wordOfNat 0x8001 }

example : BitVector.toNat 32
    ((nextState finishSignedHalfLoad initialState) .reg_out) = 0xffff8001 := by decide

def finishUnsignedLoad : Inputs :=
  { finishSignedByteLoad with
    latched_is_lb := false
    latched_is_lu := true
    mem_rdata_word := wordOfNat 0x80 }

example : BitVector.toNat 32
    ((nextState finishUnsignedLoad initialState) .reg_out) = 0x80 := by decide

def aluWritebackInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateFetch
    latched_store := true
    latched_stalu := true }

example : BitVector.toNat 32
    (writebackData aluWritebackInputs (stateWith 0 0 0 0 0x11 0 0x22)) = 0x22 := by decide

end Silean.Examples.Checks.PicoRVDatapathMemoryChecks
