import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.Increment.IncrementDerived

/-! # Enabled reset counter

This wrapping binary counter exposes its current value. It resets to
`resetValue` when `reset` is high, increments when only `enable` is high, and
otherwise retains its value. The readable construction shows the feedback;
expanded structure and certification live under `Internal/`.
-/

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

abbrev Value (width : Nat) := Fin width → Bool

@[reducible] def valueType (width : Nat) : SignalType :=
  .vector width .bit

module_ports ports (width : Nat)
    with (typeNaming : Silean.Naming.SignalTypeNaming (valueType width) :=
      .positional (valueType width)) where
  input enable : .bit,
  input reset : .bit,
  output value (schema := typeNaming) : valueType width

open ports

noncomputable def construction (width : Nat) (resetValue : Value width) :
    ModuleBuilder (ports width) Unit := do
  let enable ← input width .enable
  let reset ← input width .reset
  wire current : valueType width
  let incremented ← Increment.place current
  let stored ← EnabledResetRegister.place (signalType := valueType width) resetValue
    incremented.result enable reset
  assign current stored
  output width .value stored

noncomputable def description (width : Nat) (resetValue : Value width) :
    Description :=
  ModuleBuilder.build (Naming.ports width) (construction width resetValue)

def nextValue (width : Nat) (resetValue : Value width)
    (enable reset : Bool) (stored : Value width) : Value width :=
  bif reset then resetValue
  else bif enable then Increment.incrementValue width stored else stored

/-- The visible value is the value stored before the active clock edge. -/
def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width)
      (Register.stateMap (valueType width)) where
  readsInputs := .empty (ports width).inputs
  writesOutputs := .all (ports width).outputs
  target _ state := fun | .value => state .stored

module_cycle_contract cycleContract (width : Nat) (resetValue : Value width)
    for ports width where
  state := Register.stateMap (valueType width)
  output_rule observe := outputRule width
  state_rule where
    reads := [enable, reset]
    next := { stored := nextValue width resetValue enable reset (state .stored) }

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext output
    cases output
    exact equal

section AllowedStep

variable {width : Nat} {resetValue : Value width}
  {step : (cycleContract width resetValue).Step}
  (allowed : (cycleContract width resetValue).Allows step)

include allowed

/-- An allowed step exposes the counter value stored before the clock edge. -/
theorem value_of_allowed :
    step.outputs .value = step.currentState .stored :=
  (outputRule_holds_iff width
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- Reset has priority; otherwise enable selects increment or hold. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      nextValue width resetValue (step.inputs .enable) (step.inputs .reset)
        (step.currentState .stored) := by
  rw [allowed.2]
  rfl

theorem next_stored_of_reset (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, nextValue, reset]
  rfl

theorem next_stored_of_enabled
    (notReset : step.inputs .reset = false)
    (enabled : step.inputs .enable = true) :
    step.nextState .stored =
      Increment.incrementValue width (step.currentState .stored) := by
  rw [next_stored_of_allowed allowed, nextValue, notReset, enabled]
  rfl

theorem next_stored_of_disabled
    (notReset : step.inputs .reset = false)
    (disabled : step.inputs .enable = false) :
    step.nextState .stored = step.currentState .stored := by
  rw [next_stored_of_allowed allowed, nextValue, notReset, disabled]
  rfl

/-- Numerically, an enabled step adds one modulo `2 ^ width`. -/
theorem next_toNat_of_enabled
    (notReset : step.inputs .reset = false)
    (enabled : step.inputs .enable = true) :
    BitVector.toNat width (step.nextState .stored) =
      (BitVector.toNat width (step.currentState .stored) + 1) %
        BitVector.cardinality width := by
  rw [next_stored_of_enabled allowed notReset enabled]
  exact Increment.incrementValue_toNat width (step.currentState .stored)

end AllowedStep

end Silean.Modules.EnabledResetCounter
