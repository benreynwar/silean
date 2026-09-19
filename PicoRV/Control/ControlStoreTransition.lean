import PicoRV.Control.Internal.ControlStoreTransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Store transition

The source priority remains explicit: waiting for prefetch selects an unchanged
transition. Otherwise request start may capture the access size, completion may
return to fetch, and `setWdata` records whether a new write request must be
asserted after command clearing. The expanded typed hierarchy and verification
remain under `Internal/`. -/

namespace StoreTransition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
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
  output "transition" (← mux
    waitForPrefetch activeTransition waitTransition)

noncomputable def description : Description := build construction

end StoreTransition.Description

namespace StoreTransition

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder PlacedOutputs := do
  let child ← placeIndexed "store_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end StoreTransition

end PicoRV.Control
