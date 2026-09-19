import PicoRV.Control.ControlNextContracts
import PicoRV.Control.Internal.ControlBaselineStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.Constant.Constant

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! The baseline layer represents the unconditional assignments at the start
of the source control block. Every state field passes through except `trap`
and `decoder_pseudo_trigger`, which clear, and `decoder_trigger`, which records
completion of the current instruction fetch. Later phase children deliberately
receive this result rather than the raw state. The expanded typed hierarchy
and verification remain under `Internal/`. -/

namespace Baseline.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let falseBit ← constant .bit false
  wire fetchCompleted : .bit ←
    currentFields .mem_do_rinst &&& inputsFields .mem_done
  let result ← update stateMap ControlState.schema currentFields fun
    | .decoder_trigger => some fetchCompleted
    | .decoder_pseudo_trigger | .trap => some falseBit
    | _ => none
  output "state" result

noncomputable def description : Description := build construction

end Baseline.Description

namespace Baseline

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "control_baseline" design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

attribute [circuit_description] placeNamed place

end Baseline

end PicoRV.Control
