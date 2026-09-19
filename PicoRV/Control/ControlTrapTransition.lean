import PicoRV.Control.Internal.ControlTrapTransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! Trap is deliberately a distinct phase child even though its update is
small. It retains the complete baseline state, asserts only `trap`, and emits
no command intents. Keeping this behind the common phase boundary makes the
parent phase selection uniform. The expanded typed hierarchy is under
`Internal/`. -/

namespace TrapTransition.Description

noncomputable def construction : Builder Unit := do
  discard <| input "inputs" inputsType
  discard <| input "current" stateType
  let updated ← input "updated" stateType
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
  output "transition" result

noncomputable def description : Description := build construction

end TrapTransition.Description

namespace TrapTransition

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder PlacedOutputs := do
  let child ← placeIndexed "trap_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end TrapTransition

end PicoRV.Control
