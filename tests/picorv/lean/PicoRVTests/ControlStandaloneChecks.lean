import PicoRVTests.Fixtures.PicoRVControl
import PicoRV.ControlTheorems
import Silean.FIRRTL

namespace PicoRVTests.ControlStandaloneChecks

open Silean
open Silean.FIRRTL
open PicoRV.Control
open PicoRVTests.Fixtures.PicoRVControl

def cycle (inputs : Inputs) (state : stateMap.Values) :
    outputMap.Values × stateMap.Values :=
  cycleContract.evaluate (inputValues inputs) state

/-! ## Trap persistence

The baseline clears the trap bit on every cycle, but the trap phase asserts it
again. Consequently entering the phase raises the registered output on the
next edge, and remaining in that phase keeps it raised. -/

def firstTrapCycle := cycle idleInputs (stateIn cpuStateTrap)
def secondTrapCycle := cycle idleInputs firstTrapCycle.2

example : phase firstTrapCycle.2 = cpuStateTrap := by decide
example : firstTrapCycle.2 .trap = true := by rfl
example : phase secondTrapCycle.2 = cpuStateTrap := by decide
example : secondTrapCycle.2 .trap = true := by rfl

/-! ## Load-RS2 selector priority

With PCPI disabled, this phase has exactly three outcomes: store, register
shift, or ordinary execute. A pending prefetch distinguishes promotion into an
instruction request from the register-shift path, which retains the old
request bit. -/

def loadRs2Base : stateMap.Values :=
  commandState cpuStateLdRs2 true false false false

def afterLoadRs2 (inputs : Inputs) : Transition :=
  loadRs2Transition inputs loadRs2Base

def rs2Store := { idleInputs with is_sb_sh_sw := true }
def rs2Shift := { idleInputs with is_sll_srl_sra := true }
def rs2StoreAndShift :=
  { idleInputs with is_sb_sh_sw := true, is_sll_srl_sra := true }

example : phase (afterLoadRs2 rs2Store).state = cpuStateStmem := by decide
example : (afterLoadRs2 rs2Store).state .mem_do_rinst = true := by rfl

example : phase (afterLoadRs2 rs2Shift).state = cpuStateShift := by decide
example : (afterLoadRs2 rs2Shift).state .mem_do_rinst = false := by rfl

example : phase (afterLoadRs2 idleInputs).state = cpuStateExec := by decide
example : (afterLoadRs2 idleInputs).state .mem_do_rinst = true := by rfl

/-! Store is the earlier source branch and therefore wins if both selectors
are true. The illegal-instruction input is intentionally irrelevant here:
that source branch is compiled out when PCPI is disabled. -/

example : phase (afterLoadRs2 rs2StoreAndShift).state = cpuStateStmem := by decide
example : (afterLoadRs2 rs2StoreAndShift).state .mem_do_rinst = true := by rfl
example : afterLoadRs2 { rs2Shift with instr_trap := true } =
    afterLoadRs2 rs2Shift := by rfl

noncomputable example :
    Silean.Contracts.Cycle.ModuleCycleCertified PhaseTransition.ports :=
  TrapTransition.certified

noncomputable example :
    Silean.Contracts.Cycle.ModuleCycleCertified PhaseTransition.ports :=
  LoadRs2Transition.certified

example : TrapTransition.moduleStructure.HasNoBlackboxes :=
  TrapTransition.moduleStructure_hasNoBlackboxes

example : LoadRs2Transition.moduleStructure.HasNoBlackboxes :=
  LoadRs2Transition.moduleStructure_hasNoBlackboxes

/-! ## Current outputs and writeback

All ordinary outputs expose the pre-edge register state. `cpuregs_write` is
the exception only in the sense that it is computed combinationally: it is
true in fetch when either writeback latch is set. -/

def visibleState : stateMap.Values :=
  let state := stateMap.set (stateIn cpuStateFetch) .latched_store true
  let state := stateMap.set state .latched_rd (fiveBitsOfNat 17)
  stateMap.set state .mem_wordsize (twoBitsOfNat 2)

def visibleOutputs := (cycle idleInputs visibleState).1

example : Silean.BitVector.toNat 8 (visibleOutputs .cpu_state) = cpuStateFetch := by decide
example : visibleOutputs .latched_store = true := by rfl
example : Silean.BitVector.toNat 5 (visibleOutputs .latched_rd) = 17 := by decide
example : Silean.BitVector.toNat 2 (visibleOutputs .mem_wordsize) = 2 := by decide
example : visibleOutputs .cpuregs_write = true := by rfl

def writebackState (cpuPhase : Nat) (branch store : Bool) : stateMap.Values :=
  let state := stateMap.set (stateIn cpuPhase) .latched_branch branch
  stateMap.set state .latched_store store

example : outputValues (writebackState cpuStateFetch true false)
    .cpuregs_write = true := by rfl
example : outputValues (writebackState cpuStateFetch false true)
    .cpuregs_write = true := by rfl
example : outputValues (writebackState cpuStateFetch false false)
    .cpuregs_write = false := by rfl
example : outputValues (writebackState cpuStateExec true true)
    .cpuregs_write = false := by rfl

/-! ## Reset and next-edge capture

Reset selects fetch, clears transient latches, and clears all commands in the
next state. Outputs during that cycle still expose the old state. The final
pair of checks makes the same registered timing visible during an ordinary
fetch request. -/

def resetSource : stateMap.Values :=
  let state := commandState cpuStateExec true true true true
  let state := stateMap.set state .latched_store true
  let state := stateMap.set state .latched_branch true
  stateMap.set state .trap true

def resetCycle := cycle { idleInputs with resetn := false } resetSource

example : phase resetCycle.2 = cpuStateFetch := by decide
example : resetCycle.2 .latched_store = false := by rfl
example : resetCycle.2 .latched_branch = false := by rfl
example : resetCycle.2 .mem_do_prefetch = false := by rfl
example : resetCycle.2 .mem_do_rinst = false := by rfl
example : resetCycle.2 .mem_do_rdata = false := by rfl
example : resetCycle.2 .mem_do_wdata = false := by rfl
example : resetCycle.1 .trap = true := by rfl
example : resetCycle.2 .trap = false := by rfl

def requestCycle := cycle idleInputs (stateIn cpuStateFetch)

example : requestCycle.1 .mem_do_rinst = false := by rfl
example : requestCycle.2 .mem_do_rinst = true := by rfl

/-! The universal certification connects these executable contract examples
to the concrete registered hierarchy for arbitrary inputs and states. -/

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified ports := certified

example : moduleStructure.HasNoBlackboxes := moduleStructure_hasNoBlackboxes

example : ControlNext.moduleStructure.HasNoBlackboxes :=
  ControlNext.moduleStructure_hasNoBlackboxes

noncomputable example : RenderResult String := renderClosedCircuit naming

#guard match renderClosedCircuit naming with
  | .ok _ => true
  | .error _ => false

#guard renderModuleKey naming.key = "picorv32_control"

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule naming with
  | .error _ => false
  | .ok text =>
      ["public module picorv32_control",
       "inst storage",
       "inst next",
       "inst fetchPhase",
       "output cpuregs_write : UInt<1>",
       "output cpu_state : UInt<1>[8]",
       "output trap : UInt<1>"].all (contains text)

end PicoRVTests.ControlStandaloneChecks
