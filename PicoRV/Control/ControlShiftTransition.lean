import PicoRV.Control.Internal.ControlShiftTransitionStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.EqualsConstant.EqualsConstant

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Shift transition

Shift always marks a pending register write. Only an exactly zero five-bit
shift count returns to fetch and promotes prefetch to instruction read; a
nonzero count retains both the phase and existing read command. The expanded
typed hierarchy and verification remain under `Internal/`. -/

namespace ShiftTransition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  discard (input "current" stateType)
  let updated ← input "updated" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)
  let shiftIsZero ← Silean.Modules.EqualsConstant.place
    (inputsFields .reg_sh) (fiveBitsOfNat 0)
  let selectedPhase ← mux shiftIsZero
    (updatedFields .cpu_state) fetchState
  let selectedRinst ← mux shiftIsZero
    (updatedFields .mem_do_rinst) (updatedFields .mem_do_prefetch)
  let resultState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some selectedPhase
      | .latched_store => some trueBit
      | .mem_do_rinst => some selectedRinst
      | _ => none
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => resultState
      | .setRinst | .setRdata | .setWdata => falseBit
  output "transition" result

noncomputable def description : Description := build construction

end ShiftTransition.Description

namespace ShiftTransition

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
  let child ← placeIndexed "shift_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end ShiftTransition

end PicoRV.Control
