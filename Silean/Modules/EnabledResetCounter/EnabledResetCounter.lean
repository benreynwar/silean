import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterStructure

/-! # Enabled reset counter

This wrapping binary counter exposes its current value. On each clock edge it
resets to `resetValue` when `reset` is high, increments when only `enable` is
high, and otherwise retains its value.

The description makes the feedback path explicit: an incrementer continuously
computes the candidate next value, and an enabled reset register decides
whether to reset, load that candidate, or hold. The expanded typed hierarchy
used by verification and emission lives under `Internal/`.
-/

namespace Silean.Modules.EnabledResetCounter.Description

open Silean
open Silean.Authoring.CircuitDescription

/-- The incrementer and enabled reset register forming the counter. -/
noncomputable def construction (width : Nat) (resetValue : Value width) :
    Builder Unit := do
  let enable ← input "enable" .bit
  let reset ← input "reset" .bit
  wire current : valueType width
  let stored ← Modules.EnabledResetRegister.place
    (signalType := valueType width) resetValue
    (← Modules.Increment.place current) enable reset
  assign current stored
  output "value" stored

noncomputable def description (width : Nat) (resetValue : Value width) :
    Description :=
  build (construction width resetValue)

end Silean.Modules.EnabledResetCounter.Description

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place a counter under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (resetValue : Value width) (enable reset : Net .bit) :
    Builder (Net (valueType width)) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design width resetValue) fun
      | .enable => enable
      | .reset => reset
  pure (child .value)

/-- Place a counter using the next conventional indexed name. -/
noncomputable def place (resetValue : Value width) (enable reset : Net .bit) :
    Builder (Net (valueType width)) := do
  let child ← placeIndexed "enabled_reset_counter" (design width resetValue) fun
    | .enable => enable
    | .reset => reset
  pure (child .value)

attribute [circuit_description] placeNamed place

/-! ## Exact cycle behavior -/

def nextValue (width : Nat) (resetValue : Value width)
    (enable reset : Bool) (stored : Value width) : Value width :=
  bif reset then resetValue
  else bif enable then Increment.incrementValue width stored else stored

/-- The visible value is the value stored before the active clock edge. This
rule does not depend on the chosen reset constant. -/
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

end Silean.Modules.EnabledResetCounter
