import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitSelection
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.Register.RegisterDerived

/-! # Reset register

A reset register exposes its stored value and synchronously stores either its
ordinary input or a fixed reset value. The short construction is the readable
hardware definition; expanded structure and certification live under
`Internal/`.
-/

namespace Silean.Modules.ResetRegister

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  input reset : .bit,
  output value (name := "value_out") (schema := typeNaming) : signalType

open ports

noncomputable def construction (signalType : SignalType)
    (resetValue : signalType.Denote) : ModuleBuilder (ports signalType) Unit := do
  let value ← input signalType .value
  let reset ← input signalType .reset
  output signalType .value
    (← Register.place (← mux reset value (← constant signalType resetValue)))

noncomputable def description (signalType : SignalType)
    (resetValue : signalType.Denote) : Description :=
  ModuleBuilder.build (Naming.ports signalType)
    (construction signalType resetValue)

module_cycle_contract cycleContract (signalType : SignalType)
    (resetValue : signalType.Denote) for ports signalType where
  state := Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { value := state .stored }
  state_rule where
    reads := [reset, value]
    next := { stored := bif reset then resetValue else value }

section AllowedStep

variable {signalType : SignalType}
  {resetValue : signalType.Denote}
  {step : (cycleContract signalType resetValue).Step}
  (allowed : (cycleContract signalType resetValue).Allows step)

include allowed

/-- An allowed step exposes the value stored before the clock edge. -/
theorem value_of_allowed :
    step.outputs .value = step.currentState .stored :=
  (observeRule_holds_iff signalType resetValue
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- The next stored value is the reset value when reset is high and the input
otherwise. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .reset then resetValue else step.inputs .value := by
  rw [allowed.2]
  rfl

theorem next_stored_of_reset (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, reset]
  rfl

theorem next_stored_of_not_reset (notReset : step.inputs .reset = false) :
    step.nextState .stored = step.inputs .value := by
  rw [next_stored_of_allowed allowed, notReset]
  rfl

end AllowedStep

end Silean.Modules.ResetRegister
