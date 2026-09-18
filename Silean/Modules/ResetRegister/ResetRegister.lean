import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.ResetRegister.Internal.ResetRegisterStructure

/-! # Reset register

A reset register exposes its stored value and, on each clock edge, stores the
ordinary input unless synchronous reset is high. Reset selects the fixed
`resetValue`.

The short circuit description below is the reader-facing hardware definition.
The expanded typed structure used by verification and emission lives under
`Internal/`; `ResetRegisterTheorems.lean` connects the two and states the
public correctness results.
-/

namespace Silean.Modules.ResetRegister.Description

open Silean
open Silean.Authoring.CircuitDescription

/-- The reset value, mux, and register that make up a reset register. -/
noncomputable def construction (signalType : SignalType)
    (resetValue : signalType.Denote) : Builder Unit := do
  let value <- input "value" signalType
  let reset <- input "reset" .bit
  let constant <- Modules.Constant.placeNamed "resetValue" signalType resetValue
  let selected <- Modules.Mux.placeNamed "selection" reset value constant
  let stored <- Modules.Register.placeNamed "storage" selected
  output "value_out" stored

noncomputable def description (signalType : SignalType)
    (resetValue : signalType.Denote) : Description :=
  build (construction signalType resetValue)

end Silean.Modules.ResetRegister.Description

namespace Silean.Modules.ResetRegister

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place a reset register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (resetValue : signalType.Denote) (value : Net signalType)
    (reset : Net .bit) : Builder (Net signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType resetValue) fun
      | .value => value
      | .reset => reset
  pure (child .value)

/-- Place a reset register using the next conventional indexed name. -/
noncomputable def place (resetValue : signalType.Denote)
    (value : Net signalType) (reset : Net .bit) : Builder (Net signalType) := do
  let child ← placeIndexed "reset_register" (design signalType resetValue) fun
    | .value => value
    | .reset => reset
  pure (child .value)

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    (resetValue : signalType.Denote) for ports signalType where
  state := Modules.Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { value := state .stored }
  state_rule where
    reads := [reset, value]
    next := { stored := bif reset then resetValue else value }

end Silean.Modules.ResetRegister
