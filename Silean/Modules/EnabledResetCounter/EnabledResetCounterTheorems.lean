import Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterVerification

/-! # Enabled-reset-counter theorems

The public interface describes complete boundary steps. The recursive
incrementer, nested register state, schedules, and hierarchy assignments
remain verification details under `Internal/`.
-/

namespace Silean.Modules.EnabledResetCounter

open Silean

/-! ## Consequences of the cycle contract -/

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

/-- Reset determines the next value regardless of enable. -/
theorem next_stored_of_reset (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, nextValue, reset]
  rfl

/-- With reset low and enable high, the counter increments modulo its width. -/
theorem next_stored_of_enabled
    (notReset : step.inputs .reset = false)
    (enabled : step.inputs .enable = true) :
    step.nextState .stored =
      Increment.incrementValue width (step.currentState .stored) := by
  rw [next_stored_of_allowed allowed, nextValue, notReset, enabled]
  rfl

/-- With reset and enable both low, the counter retains its value. -/
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

/-! ## Authored and structural correctness -/

namespace Description

open Naming Authoring.CircuitDescription

/-- Elaborating the readable feedback circuit in `EnabledResetCounter.lean`
produces exactly the typed hierarchy used by verification and emission. -/
theorem authored_definition_corresponds (width : Nat)
    (resetValue : Value width) :
    Corresponds (description width resetValue)
      (EnabledResetCounter.naming width resetValue) :=
  Internal.corresponds width resetValue

end Description

/-- The concrete counter hierarchy implements its exact cycle contract at the
shared boundary-step interface. -/
theorem implements_contract (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Implements
      (moduleStructure width resetValue)
      (cycleContract width resetValue)
      (certification width resetValue).stateCorresponds :=

    (certification width resetValue).implements

end Silean.Modules.EnabledResetCounter
