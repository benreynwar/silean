import Silean.FIRRTL
import Silean.Examples.Fixtures.PicoRVControl
import Silean.Examples.PicoRV.Control.ControlCommandFinishCertified

namespace Silean.Examples.Checks.PicoRVControlCommandFinishChecks

open Silean
open Silean.FIRRTL
open Silean.Examples.PicoRV.Control
open Silean.Examples.Fixtures.PicoRVControl

def inputs (clear : Bool) (transition : Transition) : CommandFinish.inputMap.Values
  | .clear => clear
  | .transition => transition.pack

def result (clear : Bool) (transition : Transition) : stateMap.Values :=
  stateMap.unpack (((CommandFinish.cycleContract.evaluate
    (inputs clear transition) SignalMap.emptyValues).1) .state)

/-! The named layouts are lossless in both directions. These examples matter
because subsequent Control children will communicate with the same aggregate
state and transition types. -/

example (state : stateMap.Values) : stateMap.unpack (stateMap.pack state) = state := by
  exact stateMap.unpack_pack state

example (state : stateType.Denote) : stateMap.pack (stateMap.unpack state) = state := by
  exact stateMap.pack_unpack state

example (transition : Transition) : Transition.unpack transition.pack = transition := by
  exact Transition.unpack_pack transition

example (transition : transitionType.Denote) :
    (Transition.unpack transition).pack = transition := by
  exact Transition.pack_unpack transition

/-! With clearing disabled and no intents, every state field—including all
four existing commands—is retained. -/

def retainedState : stateMap.Values :=
  let state := commandState cpuStateExec true true false true
  stateMap.set state .trap true

example : result false (simpleTransition retainedState) = retainedState := by
  funext field
  cases field <;> rfl

/-! Clearing removes all commands but does not disturb unrelated proposed
state. -/

def cleared := result true (simpleTransition retainedState)

example : (cleared .mem_do_prefetch : Bool) = false := by rfl
example : (cleared .mem_do_rinst : Bool) = false := by rfl
example : (cleared .mem_do_rdata : Bool) = false := by rfl
example : (cleared .mem_do_wdata : Bool) = false := by rfl
example : (cleared .trap : Bool) = true := by rfl
example : phase cleared = cpuStateExec := by decide

/-! An intent is applied after clearing. Thus a completed old request can be
cleared and a new instruction request asserted on the same edge. Prefetch has
no intent and stays cleared. -/

def reassertedRinst := result true
  { state := retainedState, setRinst := true }

example : (reassertedRinst .mem_do_prefetch : Bool) = false := by rfl
example : (reassertedRinst .mem_do_rinst : Bool) = true := by rfl
example : (reassertedRinst .mem_do_rdata : Bool) = false := by rfl
example : (reassertedRinst .mem_do_wdata : Bool) = false := by rfl

/-! Multiple blocking intents are represented independently. Although later
reachable-state proofs should exclude conflicting data commands, the exact
cycle contract remains total for arbitrary transition values. -/

def allReasserted := result true
  { state := retainedState
    setRinst := true
    setRdata := true
    setWdata := true }

example : (allReasserted .mem_do_prefetch : Bool) = false := by rfl
example : (allReasserted .mem_do_rinst : Bool) = true := by rfl
example : (allReasserted .mem_do_rdata : Bool) = true := by rfl
example : (allReasserted .mem_do_wdata : Bool) = true := by rfl

noncomputable example : Contracts.Cycle.ModuleCycleCertified CommandFinish.ports :=
  CommandFinish.certified

example : CommandFinish.moduleStructure.HasNoBlackboxes :=
  CommandFinish.moduleStructure_hasNoBlackboxes

noncomputable example : RenderResult String :=
  renderClosedCircuit CommandFinish.naming

private def renders : Bool :=
  match renderClosedCircuit CommandFinish.naming with
  | .ok _ => true
  | .error _ => false

#guard renders
#guard renderModuleKey CommandFinish.naming.key = "picorv32_control_command_finish"

end Silean.Examples.Checks.PicoRVControlCommandFinishChecks
