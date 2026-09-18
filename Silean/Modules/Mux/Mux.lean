import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.Mux.Internal.MuxStructure

/-! # Multiplexer

The authored circuit implements selection with masking and bitwise OR. Its
exact cycle contract states the simpler implementation-independent behavior:
the output is one of the two inputs selected by the control bit.

The expanded typed structure and its verification are supporting machinery in
`Internal/`; the main reader-facing results are in `MuxTheorems.lean`.
-/

namespace Silean.Modules.Mux.Description

open Silean Naming Authoring.CircuitDescription
open scoped Authoring.CircuitLogic

/-- Ordinary do notation; existing children retain their full production identity. -/
noncomputable def construction (signalType : SignalType) : Builder Unit := do
  let select ← input "select" .bit
  let whenFalse ← input "whenFalse" signalType
  let whenTrue ← input "whenTrue" signalType
  output "result" (←
    (← whenFalse &&& (← !! select)) ||| (← whenTrue &&& select))

noncomputable def description (signalType : SignalType) := build (construction signalType)

end Silean.Modules.Mux.Description

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place a mux under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name (design signalType) fun
    | .select => select
    | .whenFalse => whenFalse
    | .whenTrue => whenTrue
  pure (child .result)

/-- Place a mux using the next conventional indexed mux name. -/
noncomputable def place (select : Net .bit)
    (whenFalse whenTrue : Net signalType) : Builder (Net signalType) := do
  let child ← placeIndexed "mux" (design signalType) fun
    | .select => select
    | .whenFalse => whenFalse
    | .whenTrue => whenTrue
  pure (child .result)

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := {
      result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

/-- Every step allowed by the cycle contract selects exactly one input value. -/
theorem result_of_allowed (signalType : SignalType)
    {step : (cycleContract signalType).Step}
    (allowed : (cycleContract signalType).Allows step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse := by
  exact (selectRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 Rule.select)

end Silean.Modules.Mux
