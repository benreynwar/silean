import PicoRV.Control.ControlBaseline
import PicoRV.Control.ControlCommandFinish
import PicoRV.Control.ControlExecuteTransition
import PicoRV.Control.ControlFetchTransition
import PicoRV.Control.ControlLoadTransition
import PicoRV.Control.ControlLoadRs1Transition
import PicoRV.Control.ControlLoadRs2Transition
import PicoRV.Control.ControlPhaseDecode
import PicoRV.Control.ControlResetAndAlignmentOverride
import PicoRV.Control.ControlStoreTransition
import PicoRV.Control.ControlShiftTransition
import PicoRV.Control.ControlTrapTransition
import PicoRV.Control.Internal.ControlNextStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Complete control-state update

This description exposes the source-level priority layers of one control
cycle. It first computes the unconditional baseline, selects the transition
for the old CPU phase, applies reset and alignment overrides, and finally
finishes or starts memory commands. Its children use conventional indexed
names; the Lean bindings below carry the explanatory names. The expanded typed
hierarchy and verification remain under `Internal/`. -/

namespace ControlNext.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
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
  output "state" state

noncomputable def description : Description := build construction

end ControlNext.Description

namespace ControlNext

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "control_next" design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

attribute [circuit_description] placeNamed place

end ControlNext

end PicoRV.Control
