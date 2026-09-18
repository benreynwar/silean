import PicoRVTests.Fixtures.PicoRVControl
import PicoRV.Control.ControlNextTheorems

namespace PicoRVTests.ControlNextChecks

open Silean
open PicoRV.Control
open PicoRVTests.Fixtures.PicoRVControl

/-! These checks exercise boundaries where assignment order matters. They are
small executable specifications alongside the universal structural proof. -/

def decodedPhase (value : Nat) : PhaseDecode.outputMap.Values :=
  (PhaseDecode.cycleContract.evaluate
    (fun | .cpu_state => stateBits value) Silean.SignalMap.emptyValues).1

example : (decodedPhase cpuStateTrap .trap : Bool) = true := by rfl
example : (decodedPhase cpuStateFetch .fetch : Bool) = true := by rfl
example : (decodedPhase cpuStateLdRs1 .loadRs1 : Bool) = true := by rfl
example : (decodedPhase cpuStateLdRs2 .loadRs2 : Bool) = true := by rfl
example : (decodedPhase cpuStateExec .execute : Bool) = true := by rfl
example : (decodedPhase cpuStateShift .shift : Bool) = true := by rfl
example : (decodedPhase cpuStateStmem .store : Bool) = true := by rfl
example : (decodedPhase cpuStateLdmem .load : Bool) = true := by rfl
example : (decodedPhase cpuStateExec .fetch : Bool) = false := by rfl

/-! An arbitrary unrecognized eight-bit phase selects no phase child. This is
why the implementation uses full-vector comparisons rather than assuming a
reachable one-hot state. -/

def noDecodedPhase : PhaseDecode.outputMap.Values
  | .trap => false
  | .fetch => false
  | .loadRs1 => false
  | .loadRs2 => false
  | .execute => false
  | .shift => false
  | .store => false
  | .load => false

example : decodedPhase 3 = noDecodedPhase := by
  funext output
  cases output <;> rfl

/-! Store and load each have three materially different handshake paths:
waiting for prefetch, starting a request, and completing one. -/

def storeWait := storeTransition idleInputs
  (commandState cpuStateStmem true false false false)
  (stateIn cpuStateStmem)

example : storeWait = simpleTransition (stateIn cpuStateStmem) := by rfl

def storeStart := storeTransition { idleInputs with instr_sh := true }
  (stateIn cpuStateStmem) (stateIn cpuStateStmem)

example : storeStart.setWdata = true := by rfl
example : wordSize storeStart.state = 1 := by decide

def storeDone := storeTransition { idleInputs with mem_done := true }
  (commandState cpuStateStmem false false false true) (stateIn cpuStateStmem)

example : phase storeDone.state = cpuStateFetch := by decide
example : (storeDone.state .decoder_trigger : Bool) = true := by rfl
example : storeDone.setWdata = false := by rfl

def loadWait := loadTransition idleInputs
  (commandState cpuStateLdmem true false false false)
  (stateIn cpuStateLdmem)

example : (loadWait.state .latched_store : Bool) = true := by rfl
example : loadWait.setRdata = false := by rfl

def loadStart := loadTransition
  { idleInputs with instr_lb := true, is_lbu_lhu_lw := false }
  (stateIn cpuStateLdmem) (stateIn cpuStateLdmem)

example : loadStart.setRdata = true := by rfl
example : wordSize loadStart.state = 2 := by decide
example : (loadStart.state .latched_is_lb : Bool) = true := by rfl

def loadDone := loadTransition { idleInputs with mem_done := true }
  (commandState cpuStateLdmem false false true false) (stateIn cpuStateLdmem)

example : phase loadDone.state = cpuStateFetch := by decide
example : (loadDone.state .decoder_pseudo_trigger : Bool) = true := by rfl
example : loadDone.setRdata = false := by rfl

/-! Branch completion and taken-ness are independent choices. Completion
controls the next phase; taken-ness controls decoder suppression and the new
instruction-read intent. -/

def branchBase : stateMap.Values :=
  stateMap.set (stateIn cpuStateExec) .decoder_trigger true

def branchResult (taken done : Bool) : Transition :=
  executeTransition
    { idleInputs with
      is_beq_bne_blt_bge_bltu_bgeu := true
      alu_out_0 := taken
      mem_done := done }
    branchBase

example : phase (branchResult false false).state = cpuStateExec := by decide
example : (branchResult false false).state .decoder_trigger = true := by rfl
example : (branchResult false false).setRinst = false := by rfl

example : phase (branchResult false true).state = cpuStateFetch := by decide
example : (branchResult false true).state .decoder_trigger = true := by rfl
example : (branchResult false true).setRinst = false := by rfl

example : phase (branchResult true false).state = cpuStateExec := by decide
example : (branchResult true false).state .decoder_trigger = false := by rfl
example : (branchResult true false).setRinst = true := by rfl

example : phase (branchResult true true).state = cpuStateFetch := by decide
example : (branchResult true true).state .decoder_trigger = false := by rfl
example : (branchResult true true).setRinst = true := by rfl

/-! Alignment reads the current commands and addresses. Word accesses reject
either low address bit; instruction fetches use the same four-byte rule. -/

def wordReadState : stateMap.Values :=
  stateMap.set (commandState cpuStateLdmem false false true false)
    .mem_wordsize (twoBitsOfNat 0)

example : dataMisaligned { idleInputs with reg_op1 := wordOfNat 2 }
    wordReadState = true := by rfl
example : dataMisaligned { idleInputs with reg_op1 := wordOfNat 4 }
    wordReadState = false := by rfl
example : instructionMisaligned { idleInputs with reg_pc := wordOfNat 2 }
    (commandState cpuStateFetch false true false false) = true := by rfl

/-! Reset wins over a simultaneous misalignment. With reset inactive,
misalignment happens after phase selection: only the phase changes, while the
selected transition's other state updates and command intents remain. -/

def resetWins : Transition :=
  resetAndAlignmentTransition
    { idleInputs with resetn := false, reg_op1 := wordOfNat 2 }
    wordReadState (baselineState idleInputs wordReadState)
    { state := stateMap.set (stateIn cpuStateExec) .latched_store true
      setWdata := true }

example : phase resetWins.state = cpuStateFetch := by decide
example : (resetWins.state .latched_store : Bool) = false := by rfl
example : resetWins.setWdata = false := by rfl

def alignmentAfterSelection : Transition :=
  resetAndAlignmentTransition
    { idleInputs with reg_op1 := wordOfNat 2 }
    wordReadState (baselineState idleInputs wordReadState)
    { state := stateMap.set (stateIn cpuStateExec) .latched_store true
      setWdata := true }

example : phase alignmentAfterSelection.state = cpuStateTrap := by decide
example : (alignmentAfterSelection.state .latched_store : Bool) = true := by rfl
example : alignmentAfterSelection.setWdata = true := by rfl

/-! Command clearing precedes intent application, so completion can clear an
old request and reassert a newly selected request on the same edge. -/

def clearedThenReasserted := finishCommands true
  { state := commandState cpuStateLdmem true true true true
    setRdata := true }

example : (clearedThenReasserted .mem_do_prefetch : Bool) = false := by rfl
example : (clearedThenReasserted .mem_do_rinst : Bool) = false := by rfl
example : (clearedThenReasserted .mem_do_rdata : Bool) = true := by rfl
example : (clearedThenReasserted .mem_do_wdata : Bool) = false := by rfl

/-! This is the universal result behind the focused examples: for arbitrary
inputs and arbitrary packed current state, the hierarchy's output is exactly
`Control.nextState`. -/

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified ControlNext.ports :=
  ControlNext.certified

example : Baseline.moduleStructure.HasNoBlackboxes :=
  Baseline.moduleStructure_hasNoBlackboxes
example : PhaseDecode.moduleStructure.HasNoBlackboxes :=
  PhaseDecode.moduleStructure_hasNoBlackboxes
example : ExecuteTransition.moduleStructure.HasNoBlackboxes :=
  ExecuteTransition.moduleStructure_hasNoBlackboxes
example : StoreTransition.moduleStructure.HasNoBlackboxes :=
  StoreTransition.moduleStructure_hasNoBlackboxes
example : LoadTransition.moduleStructure.HasNoBlackboxes :=
  LoadTransition.moduleStructure_hasNoBlackboxes
example : Alignment.moduleStructure.HasNoBlackboxes :=
  Alignment.moduleStructure_hasNoBlackboxes
example : ResetAndAlignmentOverride.moduleStructure.HasNoBlackboxes :=
  ResetAndAlignmentOverride.moduleStructure_hasNoBlackboxes

/-! Every phase child is now concrete, so the complete combinational parent is
closed as well as universally certified. -/

example : ControlNext.moduleStructure.HasNoBlackboxes :=
  ControlNext.moduleStructure_hasNoBlackboxes

end PicoRVTests.ControlNextChecks
