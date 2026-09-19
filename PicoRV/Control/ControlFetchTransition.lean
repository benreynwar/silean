import PicoRV.Control.Internal.ControlFetchTransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Fetch transition

Fetch deliberately reads the pre-edge `decoder_trigger`. The common state
captures the destination register and clears transient metadata. An absent
decode requests an instruction and stays in fetch. A present decode selects
JAL (reissue instruction read and mark a branch) or the ordinary/JALR path
(enter load-RS1 and enable prefetch except for JALR). The expanded typed
hierarchy and verification remain under `Internal/`. -/

namespace FetchTransition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let wordSize ← constant (.vector 2 .bit) (twoBitsOfNat 0)
  let loadRs1State ← constant (.vector 8 .bit) (stateBits cpuStateLdRs1)
  let notDecoder ← !! (currentFields .decoder_trigger)
  let notJalr ← !! (inputsFields .instr_jalr)

  let commonState ← update stateMap ControlState.schema
    updatedFields fun
      | .latched_store | .latched_stalu | .latched_branch
      | .latched_is_lu | .latched_is_lh | .latched_is_lb => some falseBit
      | .latched_rd => some (inputsFields .decoded_rd)
      | .mem_wordsize => some wordSize
      | .mem_do_rinst => some notDecoder
      | _ => none
  let commonFields ← split ControlState.layout commonState
  let jalState ← update stateMap ControlState.schema
    commonFields fun
      | .latched_branch | .mem_do_rinst => some trueBit
      | _ => none
  let ordinaryState ← update stateMap ControlState.schema
    commonFields fun
      | .cpu_state => some loadRs1State
      | .mem_do_prefetch => some notJalr
      | .mem_do_rinst => some falseBit
      | _ => none
  let decodedState ← mux (inputsFields .instr_jal) ordinaryState jalState
  let finalState ← mux notDecoder decodedState commonState
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => finalState
      | .setRinst | .setRdata | .setWdata => falseBit
  output "transition" result

noncomputable def description : Description := build construction

end FetchTransition.Description

namespace FetchTransition

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
  let child ← placeIndexed "fetch_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end FetchTransition

end PicoRV.Control
