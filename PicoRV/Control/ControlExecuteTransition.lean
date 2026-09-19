import PicoRV.Control.Internal.ControlExecuteTransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Execute transition

Execute has two complete transition candidates. The branch candidate keeps the
source's independent priorities visible: `mem_done` may return to fetch, while
a taken branch independently suppresses `decoder_trigger` and raises
`setRinst`. The final mux selects the branch candidate by instruction class.
The expanded typed hierarchy and verification remain under `Internal/`. -/

namespace ExecuteTransition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  discard (input "current" stateType)
  let updated ← input "updated" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let zeroRd ← constant (.vector 5 .bit) (fiveBitsOfNat 0)
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)

  let branchPhase ← mux (inputsFields .mem_done)
    (updatedFields .cpu_state) fetchState
  let branchDecoder ← mux (inputsFields .alu_out_0)
    (updatedFields .decoder_trigger) falseBit
  let branchState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some branchPhase
      | .latched_store | .latched_branch => some (inputsFields .alu_out_0)
      | .latched_rd => some zeroRd
      | .decoder_trigger => some branchDecoder
      | _ => none
  let branchTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => branchState
      | .setRinst => inputsFields .alu_out_0
      | .setRdata | .setWdata => falseBit

  let ordinaryState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some fetchState
      | .latched_store | .latched_stalu => some trueBit
      | .latched_branch => some (inputsFields .instr_jalr)
      | _ => none
  let ordinaryTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => ordinaryState
      | .setRinst | .setRdata | .setWdata => falseBit

  output "transition" (← mux
    (inputsFields .is_beq_bne_blt_bge_bltu_bgeu)
    ordinaryTransition branchTransition)

noncomputable def description : Description := build construction

end ExecuteTransition.Description

namespace ExecuteTransition

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
  let child ← placeIndexed "execute_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end ExecuteTransition

end PicoRV.Control
