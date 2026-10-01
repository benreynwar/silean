import PicoRV.Control.ControlBaselineDerived
import PicoRV.Control.ControlCommandFinishDerived
import PicoRV.Control.ControlExecuteTransitionDerived
import PicoRV.Control.ControlFetchTransitionDerived
import PicoRV.Control.ControlLoadTransitionDerived
import PicoRV.Control.ControlLoadRs1TransitionDerived
import PicoRV.Control.ControlLoadRs2TransitionDerived
import PicoRV.Control.ControlPhaseDecodeDerived
import PicoRV.Control.ControlResetAndAlignmentOverrideDerived
import PicoRV.Control.ControlStoreTransitionDerived
import PicoRV.Control.ControlShiftTransitionDerived
import PicoRV.Control.ControlTrapTransitionDerived
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace ControlNext

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  output state (schema := ControlState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  nextState (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack (outputState step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-! # Complete control-state update

This description exposes the source-level priority layers of one control
cycle. It first computes the unconditional baseline, selects the transition
for the old CPU phase, applies reset and alignment overrides, and finally
finishes or starts memory commands. Its children use conventional indexed
names; the Lean bindings below carry the explanatory names. The expanded typed
hierarchy and verification remain under `Internal/`. -/

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let falseBit ← constant .bit false

  let baseline ← Baseline.place inputs current
  let phase ← PhaseDecode.place (currentFields .cpu_state)
  let trap ← TrapTransition.place inputs current baseline
  let fetch ← FetchTransition.place inputs current baseline
  let loadRs1 ← LoadRs1Transition.place inputs current baseline
  let loadRs2 ← LoadRs2Transition.place inputs current baseline
  let execute ← ExecuteTransition.place inputs current baseline
  let shift ← ShiftTransition.place inputs current baseline
  let store ← StoreTransition.place inputs current baseline
  let load ← LoadTransition.place inputs current baseline

  let defaultTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => baseline
      | .setRinst | .setRdata | .setWdata => falseBit
  let selected ← mux phase.load defaultTransition load.transition
  let selected ← mux phase.store selected store.transition
  let selected ← mux phase.shift selected shift.transition
  let selected ← mux phase.execute selected execute.transition
  let selected ← mux phase.loadRs2 selected loadRs2.transition
  let selected ← mux phase.loadRs1 selected loadRs1.transition
  let selected ← mux phase.fetch selected fetch.transition
  let selected ← mux phase.trap selected trap.transition

  let overridden ← ResetAndAlignmentOverride.place
    inputs current baseline selected
  let clearCommands ← (← !! (inputsFields .resetn)) |||
    (inputsFields .mem_done)
  let state ← CommandFinish.place clearCommands overridden.transition
  output .state state

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end ControlNext

end PicoRV.Control
