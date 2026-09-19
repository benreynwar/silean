import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.BitMux.Internal.BitMuxStructure

/-! # One-bit multiplexer

The authored circuit spells out the four Boolean gates. The exact cycle
contract below states the simpler selection behavior independently of that
implementation. Expanded typed wiring and certification remain under
`Internal/`.
-/

namespace Silean.Modules.BitMux

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring.CircuitLogic

namespace Description

noncomputable def construction : Builder Unit := do
  let select ← input "select" .bit
  let whenFalse ← input "whenFalse" .bit
  let whenTrue ← input "whenTrue" .bit
  output "result" (←
    (← whenFalse &&& (← !! select)) ||| (← whenTrue &&& select))

noncomputable def description : Description := build construction

end Description

/-! ## Placement -/

/-- Place a bit mux under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (select whenFalse whenTrue : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .select => select
    | .whenFalse => whenFalse
    | .whenTrue => whenTrue
  pure (child .result)

/-- Place a bit mux using the next conventional indexed name. -/
noncomputable def place (select whenFalse whenTrue : Net .bit) :
    Builder (Net .bit) := do
  let child ← placeIndexed "bit_mux" design fun
    | .select => select
    | .whenFalse => whenFalse
    | .whenTrue => whenTrue
  pure (child .result)

attribute [circuit_description] placeNamed place


module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := { result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

/-- Every contract-allowed bit-mux step selects the requested input. -/
theorem result_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  (selectRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .select)

end Silean.Modules.BitMux
