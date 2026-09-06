import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Increment.Increment

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring

/-! A wrapping binary counter which increments when enabled and synchronously
resets to a fixed bit-vector value. -/

abbrev Value (width : Nat) := Fin width → Bool

@[reducible] def valueType (width : Nat) : SignalType :=
  .vector width .bit

module_ports ports (width : Nat) where
  input enable : .bit,
  input reset : .bit,
  output value : valueType width

end Silean.Modules.EnabledResetCounter

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design EnabledResetCounter (width : Nat)
    (resetValue : EnabledResetCounter.Value width)
    (specialization := .natural width ::
      Constant.Naming.parameters (EnabledResetCounter.valueType width) resetValue) where
  boundary (EnabledResetCounter.ports width)
    (naming := EnabledResetCounter.Naming.ports width)
  instances {
    -- Continuously computes the candidate incremented value.
    increment := Increment.design width,
    -- Retains, loads, or resets the counter value.
    storage := EnabledResetRegister.design
      (EnabledResetCounter.valueType width) resetValue }
  wiring {
    outputs {
      .value := storage.value }
    instance (.increment) {
      .value := storage.value }
    instance (.storage) {
      .value := increment.result,
      .enable := input.enable,
      .reset := input.reset }
  }

end Silean.Modules

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring

/-! ## Exact cycle behavior -/

def nextValue (width : Nat) (resetValue : Value width)
    (enable reset : Bool) (stored : Value width) : Value width :=
  bif reset then resetValue
  else bif enable then Increment.incrementValue width stored else stored

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
  simp only [Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext output
    cases output
    exact equal

@[simp] theorem stateRule_apply_stored (width : Nat)
    (resetValue : Value width) (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values) :
    (stateRule width resetValue).apply inputs state .stored =
      nextValue width resetValue (inputs .enable) (inputs .reset)
        (state .stored) := by
  rfl

theorem next_stored_of_reset (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (reset : inputs .reset = true) :
    (stateRule width resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, nextValue, reset]
  rfl

theorem next_stored_of_enabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    (stateRule width resetValue).apply inputs state .stored =
      Increment.incrementValue width (state .stored) := by
  rw [stateRule_apply_stored, nextValue, notReset, enabled]
  rfl

theorem next_stored_of_disabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (disabled : inputs .enable = false) :
    (stateRule width resetValue).apply inputs state .stored = state .stored := by
  rw [stateRule_apply_stored, nextValue, notReset, disabled]
  rfl

theorem next_toNat_of_enabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    BitVector.toNat width ((stateRule width resetValue).apply inputs state .stored) =
      (BitVector.toNat width (state .stored) + 1) % BitVector.cardinality width := by
  rw [next_stored_of_enabled width resetValue inputs state notReset enabled]
  exact Increment.incrementValue_toNat width (state .stored)

end Silean.Modules.EnabledResetCounter
