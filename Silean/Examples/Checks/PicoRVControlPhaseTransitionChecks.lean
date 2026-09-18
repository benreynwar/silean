import Silean.Examples.Fixtures.PicoRVControl
import Silean.Examples.PicoRV.Control.ControlFetchTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlLoadRs1TransitionTheorems
import Silean.Examples.PicoRV.Control.ControlShiftTransitionTheorems

namespace Silean.Examples.Checks.PicoRVControlPhaseTransitionChecks

open Silean
open Silean.Examples.PicoRV.Control
open Silean.Examples.Fixtures.PicoRVControl

/-! ## Fetch: wait for a decode, then choose the next action

`fetchTransition` reads `decoder_trigger` from the current state. While no
decoded instruction is available, it requests an instruction and remains in
fetch. The common fetch work also clears the transient instruction latches and
captures the decoder's destination register. -/

def fetchBase : stateMap.Values :=
  let state := stateIn cpuStateFetch
  let state := stateMap.set state .latched_store true
  let state := stateMap.set state .latched_stalu true
  stateMap.set state .latched_branch true

def fetchRequesting : Transition :=
  fetchTransition { idleInputs with decoded_rd := fiveBitsOfNat 9 }
    (stateIn cpuStateFetch) fetchBase

example : phase fetchRequesting.state = cpuStateFetch := by decide
example : fetchRequesting.state .mem_do_rinst = true := by rfl
example : fetchRequesting.state .latched_store = false := by rfl
example : fetchRequesting.state .latched_stalu = false := by rfl
example : fetchRequesting.state .latched_branch = false := by rfl
example : fetchRequesting.state .latched_rd = fiveBitsOfNat 9 := by rfl

/-! An already-active instruction request takes the same path while the
decoder is still unavailable. In particular, the old request bit is not used
as a second selector: fetch keeps the request asserted. -/

def fetchWaiting : Transition :=
  fetchTransition idleInputs
    (commandState cpuStateFetch false true false false) fetchBase

example : phase fetchWaiting.state = cpuStateFetch := by decide
example : fetchWaiting.state .mem_do_rinst = true := by rfl

/-! Once `decoder_trigger` is set, an ordinary instruction advances to
load-RS1. Fetch starts a prefetch for the following instruction and stops the
current instruction request. -/

def decodedFetch : stateMap.Values :=
  stateMap.set (stateIn cpuStateFetch) .decoder_trigger true

def fetchOrdinary : Transition :=
  fetchTransition idleInputs decodedFetch (stateIn cpuStateFetch)

example : phase fetchOrdinary.state = cpuStateLdRs1 := by decide
example : fetchOrdinary.state .mem_do_prefetch = true := by rfl
example : fetchOrdinary.state .mem_do_rinst = false := by rfl

/-! JAL is handled directly in fetch: it stays in fetch, marks the result as a
branch writeback, and immediately requests another instruction. JALR instead
needs RS1, so it advances to load-RS1 and deliberately suppresses prefetch. -/

def fetchJal : Transition :=
  fetchTransition { idleInputs with instr_jal := true }
    decodedFetch (stateIn cpuStateFetch)

example : phase fetchJal.state = cpuStateFetch := by decide
example : fetchJal.state .latched_branch = true := by rfl
example : fetchJal.state .mem_do_rinst = true := by rfl

def fetchJalr : Transition :=
  fetchTransition { idleInputs with instr_jalr := true }
    decodedFetch (stateIn cpuStateFetch)

example : phase fetchJalr.state = cpuStateLdRs1 := by decide
example : fetchJalr.state .mem_do_prefetch = false := by rfl
example : fetchJalr.state .mem_do_rinst = false := by rfl

/-! ## Load-RS1: instruction-class priority

The selector chain is intentionally total and ordered. These examples use a
pending prefetch and no instruction request so that branches which promote the
prefetch (`mem_do_rinst := mem_do_prefetch`) are visibly different from
branches which retain `mem_do_rinst`. -/

def loadRs1Base : stateMap.Values :=
  commandState cpuStateLdRs1 true false false false

def selectAfterRs1 (inputs : Inputs) : Transition :=
  loadRs1Transition inputs loadRs1Base

def trapInstruction := { idleInputs with instr_trap := true }
def directInstruction := { idleInputs with is_lui_auipc_jal := true }
def loadInstruction := { idleInputs with is_lb_lh_lw_lbu_lhu := true }
def immediateShiftInstruction := { idleInputs with is_slli_srli_srai := true }
def immediateAluInstruction :=
  { idleInputs with is_jalr_addi_slti_sltiu_xori_ori_andi := true }
def storeInstruction := { idleInputs with is_sb_sh_sw := true }
def registerShiftInstruction := { idleInputs with is_sll_srl_sra := true }

example : phase (selectAfterRs1 trapInstruction).state = cpuStateTrap := by decide
example : (selectAfterRs1 trapInstruction).state .mem_do_rinst = false := by rfl

example : phase (selectAfterRs1 directInstruction).state = cpuStateExec := by decide
example : (selectAfterRs1 directInstruction).state .mem_do_rinst = true := by rfl

example : phase (selectAfterRs1 loadInstruction).state = cpuStateLdmem := by decide
example : (selectAfterRs1 loadInstruction).state .mem_do_rinst = true := by rfl

example : phase (selectAfterRs1 immediateShiftInstruction).state =
    cpuStateShift := by decide
example : (selectAfterRs1 immediateShiftInstruction).state .mem_do_rinst =
    false := by rfl

example : phase (selectAfterRs1 immediateAluInstruction).state =
    cpuStateExec := by decide
example : (selectAfterRs1 immediateAluInstruction).state .mem_do_rinst = true := by
  rfl

example : phase (selectAfterRs1 storeInstruction).state = cpuStateStmem := by decide
example : (selectAfterRs1 storeInstruction).state .mem_do_rinst = true := by rfl

example : phase (selectAfterRs1 registerShiftInstruction).state =
    cpuStateShift := by decide
example : (selectAfterRs1 registerShiftInstruction).state .mem_do_rinst =
    false := by rfl

example : phase (selectAfterRs1 idleInputs).state = cpuStateExec := by decide
example : (selectAfterRs1 idleInputs).state .mem_do_rinst = true := by rfl

/-! Overlapping selectors are not assumed impossible by the hardware or its
proof. Each example below isolates one adjacent priority decision: the class
named first wins over the class named second. -/

def trapAndDirect :=
  { idleInputs with instr_trap := true, is_lui_auipc_jal := true }
def directAndLoad :=
  { idleInputs with is_lui_auipc_jal := true, is_lb_lh_lw_lbu_lhu := true }
def loadAndImmediateShift :=
  { idleInputs with is_lb_lh_lw_lbu_lhu := true, is_slli_srli_srai := true }
def immediateShiftAndAlu :=
  { idleInputs with
    is_slli_srli_srai := true
    is_jalr_addi_slti_sltiu_xori_ori_andi := true }
def immediateAluAndStore :=
  { idleInputs with
    is_jalr_addi_slti_sltiu_xori_ori_andi := true
    is_sb_sh_sw := true }
def storeAndRegisterShift :=
  { idleInputs with is_sb_sh_sw := true, is_sll_srl_sra := true }

example : phase (selectAfterRs1 trapAndDirect).state = cpuStateTrap := by decide
example : phase (selectAfterRs1 directAndLoad).state = cpuStateExec := by decide
example : phase (selectAfterRs1 loadAndImmediateShift).state =
    cpuStateLdmem := by decide
example : phase (selectAfterRs1 immediateShiftAndAlu).state =
    cpuStateShift := by decide
example : phase (selectAfterRs1 immediateAluAndStore).state =
    cpuStateExec := by decide
example : phase (selectAfterRs1 storeAndRegisterShift).state =
    cpuStateStmem := by decide

/-! ## Shift: finish only when the remaining amount is zero

A zero shift amount returns to fetch and promotes a pending prefetch into an
instruction read. A nonzero amount stays in shift and leaves both command bits
alone. Both paths mark the eventual result for register writeback. -/

def shiftBase : stateMap.Values :=
  commandState cpuStateShift true false false false

def shiftFinished : Transition :=
  shiftTransition { idleInputs with reg_sh := fiveBitsOfNat 0 } shiftBase

example : phase shiftFinished.state = cpuStateFetch := by decide
example : shiftFinished.state .mem_do_rinst = true := by rfl
example : shiftFinished.state .latched_store = true := by rfl

def shiftContinues : Transition :=
  shiftTransition { idleInputs with reg_sh := fiveBitsOfNat 3 } shiftBase

example : phase shiftContinues.state = cpuStateShift := by decide
example : shiftContinues.state .mem_do_rinst = false := by rfl
example : shiftContinues.state .mem_do_prefetch = true := by rfl
example : shiftContinues.state .latched_store = true := by rfl

def shiftFinishedWithoutPrefetch : Transition :=
  shiftTransition idleInputs
    (commandState cpuStateShift false true false false)

example : phase shiftFinishedWithoutPrefetch.state = cpuStateFetch := by decide
example : shiftFinishedWithoutPrefetch.state .mem_do_rinst = false := by rfl

/-! These witnesses connect the executable examples above to the hardware:
each concrete hierarchy implements the corresponding transition contract for
all inputs and proposed states, and contains no behavioral blackboxes. -/

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified PhaseTransition.ports :=
  FetchTransition.certified

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified PhaseTransition.ports :=
  LoadRs1Transition.certified

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified PhaseTransition.ports :=
  ShiftTransition.certified

example : FetchTransition.moduleStructure.HasNoBlackboxes :=
  FetchTransition.moduleStructure_hasNoBlackboxes

example : LoadRs1Transition.moduleStructure.HasNoBlackboxes :=
  LoadRs1Transition.moduleStructure_hasNoBlackboxes

example : ShiftTransition.moduleStructure.HasNoBlackboxes :=
  ShiftTransition.moduleStructure_hasNoBlackboxes

end Silean.Examples.Checks.PicoRVControlPhaseTransitionChecks
