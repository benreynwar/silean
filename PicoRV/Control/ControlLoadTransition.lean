import PicoRV.Control.Internal.ControlLoadTransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Load transition

The source priority remains explicit. A pending prefetch keeps the phase and
only latches that a memory operation is in progress. Otherwise request start
captures the load size and signedness, while completion independently returns
to fetch and raises both decoder triggers. The expanded typed hierarchy and
verification remain under `Internal/`. -/

namespace LoadTransition.Description

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
  let notRdata ← !! (currentFields .mem_do_rdata)
  let byteLoad ← inputsFields .instr_lb ||| inputsFields .instr_lbu
  let halfLoad ← inputsFields .instr_lh ||| inputsFields .instr_lhu
  let halfOrWord ← mux halfLoad sizeWord sizeHalf
  let loadSize ← mux byteLoad halfOrWord sizeByte
  let capturedWordsize ← mux notRdata
    (updatedFields .mem_wordsize) loadSize
  let capturedUnsigned ← mux notRdata
    (updatedFields .latched_is_lu) (inputsFields .is_lbu_lhu_lw)
  let capturedHalf ← mux notRdata
    (updatedFields .latched_is_lh) (inputsFields .instr_lh)
  let capturedByte ← mux notRdata
    (updatedFields .latched_is_lb) (inputsFields .instr_lb)
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
      | .latched_store => some trueBit
      | .latched_is_lu => some capturedUnsigned
      | .latched_is_lh => some capturedHalf
      | .latched_is_lb => some capturedByte
      | .mem_wordsize => some capturedWordsize
      | .decoder_trigger => some finishedDecoder
      | .decoder_pseudo_trigger => some finishedPseudo
      | _ => none
  let activeTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => activeState
      | .setRdata => notRdata
      | .setRinst | .setWdata => falseBit
  let waitState ← update stateMap ControlState.schema
    updatedFields fun
      | .latched_store => some trueBit
      | _ => none
  let waitTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => waitState
      | .setRinst | .setRdata | .setWdata => falseBit
  output "transition" (← mux
    waitForPrefetch activeTransition waitTransition)

noncomputable def description : Description := build construction

end LoadTransition.Description

namespace LoadTransition

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
  let child ← placeIndexed "load_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end LoadTransition

end PicoRV.Control
