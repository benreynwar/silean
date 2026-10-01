import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace StoreTransition

abbrev cycleContract := PhaseTransition.cycleContract storeTransition

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      (storeTransition (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff storeTransition
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! # Store transition

The source priority remains explicit: waiting for prefetch selects an unchanged
transition. Otherwise request start may capture the access size, completion may
return to fetch, and `setWdata` records whether a new write request must be
asserted after command clearing. The expanded typed hierarchy and verification
remain under `Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let updated ← input .updated
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let sizeWord ← constant (.vector 2 .bit) (twoBitsOfNat 0)
  let sizeHalf ← constant (.vector 2 .bit) (twoBitsOfNat 1)
  let sizeByte ← constant (.vector 2 .bit) (twoBitsOfNat 2)
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)

  let waitForPrefetch ← currentFields .mem_do_prefetch &&&
    (← !! (inputsFields .mem_done))
  let notWdata ← !! (currentFields .mem_do_wdata)
  let halfOrWord ← mux (inputsFields .instr_sh) sizeWord sizeHalf
  let storeSize ← mux (inputsFields .instr_sb) halfOrWord sizeByte
  let startedWordsize ← mux notWdata
    (updatedFields .mem_wordsize) storeSize
  let finish ← (← !! (currentFields .mem_do_prefetch)) &&&
    (inputsFields .mem_done)
  let finishedPhase ← mux finish (updatedFields .cpu_state) fetchState
  let finishedDecoder ← mux finish
    (updatedFields .decoder_trigger) trueBit
  let finishedPseudo ← mux finish
    (updatedFields .decoder_pseudo_trigger) trueBit

  let activeState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some finishedPhase
      | .mem_wordsize => some startedWordsize
      | .decoder_trigger => some finishedDecoder
      | .decoder_pseudo_trigger => some finishedPseudo
      | _ => none
  let activeTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => activeState
      | .setWdata => notWdata
      | .setRinst | .setRdata => falseBit
  let waitTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => updated
      | .setRinst | .setRdata | .setWdata => falseBit
  output .transition (← mux
    waitForPrefetch activeTransition waitTransition)

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end StoreTransition

end PicoRV.Control
