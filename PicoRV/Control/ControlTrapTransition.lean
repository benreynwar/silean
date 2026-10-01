import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

def trapTransitionChild (_ : Inputs) (_ : stateMap.Values)
    (updated : stateMap.Values) : Transition :=
  simpleTransition (stateMap.set updated .trap true)

namespace TrapTransition

abbrev cycleContract := PhaseTransition.cycleContract trapTransitionChild

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      (trapTransitionChild (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff trapTransitionChild
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! Trap is deliberately a distinct phase child even though its update is
small. It retains the complete baseline state, asserts only `trap`, and emits
no command intents. Keeping this behind the common phase boundary makes the
parent phase selection uniform. The expanded typed hierarchy is under
`Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  discard <| input .inputs
  discard <| input .current
  let updated ← input .updated
  let updatedFields ← split ControlState.layout updated
  let trueBit ← constant .bit true
  let resultState ← update stateMap ControlState.schema
    updatedFields fun
      | .trap => some trueBit
      | _ => none
  let falseBit ← constant .bit false
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => resultState
      | .setRinst | .setRdata | .setWdata => falseBit
  output .transition result

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end TrapTransition

end PicoRV.Control
