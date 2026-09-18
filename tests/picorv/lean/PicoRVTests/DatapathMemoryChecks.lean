import PicoRVTests.Fixtures.PicoRVDatapath

namespace PicoRVTests.DatapathMemoryChecks

open Silean
open PicoRV.Datapath
open PicoRVTests.Fixtures.PicoRVDatapath

def startLoadInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateLdmem, decoded_imm := wordOfNat 12 }

def loadAddressState := nextState startLoadInputs (stateWith 0 0 0x1000 0 0 0 0)
example : Silean.BitVector.toNat 32 (loadAddressState .reg_op1) = 0x100c := by decide

def startStoreInputs : Inputs :=
  { idleInputs with cpu_state := stateBits cpuStateStmem, decoded_imm := wordOfNat 20 }

def storeAddressState := nextState startStoreInputs (stateWith 0 0 0x2000 0 0 0 0)
example : Silean.BitVector.toNat 32 (storeAddressState .reg_op1) = 0x2014 := by decide

/-! Address formation happens exactly once. A pending prefetch stalls the
memory phase, and an already-active read or write command retains the address
instead of adding the immediate again. -/

def stalledPrefetchInputs : Inputs :=
  { startLoadInputs with mem_do_prefetch := true, mem_done := false }

def activeLoadInputs : Inputs :=
  { startLoadInputs with mem_do_rdata := true }

def activeStoreInputs : Inputs :=
  { startStoreInputs with mem_do_wdata := true }

example : Silean.BitVector.toNat 32
    ((nextState stalledPrefetchInputs (stateWith 0 0 0x1000 0 0 0 0)) .reg_op1) =
      0x1000 := by decide
example : Silean.BitVector.toNat 32
    ((nextState activeLoadInputs (stateWith 0 0 0x100c 0 0 0 0)) .reg_op1) =
      0x100c := by decide
example : Silean.BitVector.toNat 32
    ((nextState activeStoreInputs (stateWith 0 0 0x2014 0 0 0 0)) .reg_op1) =
      0x2014 := by decide

def finishSignedByteLoad : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateLdmem
    mem_do_rdata := true
    mem_done := true
    latched_is_lb := true
    mem_rdata_word := wordOfNat 0x80 }

def loadedByte := nextState finishSignedByteLoad initialState
example : Silean.BitVector.toNat 32 (loadedByte .reg_out) = 0xffffff80 := by decide

def finishSignedHalfLoad : Inputs :=
  { finishSignedByteLoad with
    latched_is_lb := false
    latched_is_lh := true
    mem_rdata_word := wordOfNat 0x8001 }

example : Silean.BitVector.toNat 32
    ((nextState finishSignedHalfLoad initialState) .reg_out) = 0xffff8001 := by decide

def finishUnsignedLoad : Inputs :=
  { finishSignedByteLoad with
    latched_is_lb := false
    latched_is_lu := true
    mem_rdata_word := wordOfNat 0x80 }

example : Silean.BitVector.toNat 32
    ((nextState finishUnsignedLoad initialState) .reg_out) = 0x80 := by decide

/-! The load formatter is total. Positive signed values remain positive, and
if no width selector is latched the configured source writes zero. -/

def finishPositiveSignedByte : Inputs :=
  { finishSignedByteLoad with mem_rdata_word := wordOfNat 0x7f }

def finishWithoutWidth : Inputs :=
  { finishSignedByteLoad with latched_is_lb := false }

example : Silean.BitVector.toNat 32
    ((nextState finishPositiveSignedByte initialState) .reg_out) = 0x7f := by decide
example : Silean.BitVector.toNat 32
    ((nextState finishWithoutWidth (stateWith 0 0 0 0 0x1234 0 0)) .reg_out) = 0 := by
  decide

def aluWritebackInputs : Inputs :=
  { idleInputs with
    cpu_state := stateBits cpuStateFetch
    latched_store := true
    latched_stalu := true }

example : Silean.BitVector.toNat 32
    (writebackData aluWritebackInputs (stateWith 0 0 0 0 0x11 0 0x22)) = 0x22 := by decide

end PicoRVTests.DatapathMemoryChecks
