import Silean.Modules.EnabledResetRegister.Internal.EnabledResetRegisterVerification

/-! # Enabled-reset-register theorems

These are the reader-facing guarantees for the stateful circuit in
`EnabledResetRegister.lean`. The cycle behavior distinguishes the contract's
behavioral state from the recursively derived structural state; certification
relates the two without asserting that they are the same type or representation.
-/

namespace Silean.Modules.EnabledResetRegister

open Silean

/-! ## Consequences of the cycle contract -/

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

/-- An allowed step gives synchronous reset priority over loading a new value,
and otherwise retains the current value. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .reset then resetValue
      else bif step.inputs .enable then step.inputs .value
      else step.currentState .stored := by
  rw [allowed.2]
  rfl

/-- Reset determines the next stored value, regardless of enable. -/
theorem next_stored_of_reset
    (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, reset]
  rfl

/-- With reset low and enable high, the input becomes the next stored value. -/
theorem next_stored_of_enabled
    (notReset : step.inputs .reset = false)
    (enabled : step.inputs .enable = true) :
    step.nextState .stored = step.inputs .value := by
  rw [next_stored_of_allowed allowed, notReset, enabled]
  rfl

/-- With reset and enable both low, the stored value is retained. -/
theorem next_stored_of_disabled
    (notReset : step.inputs .reset = false)
    (disabled : step.inputs .enable = false) :
    step.nextState .stored = step.currentState .stored := by
  rw [next_stored_of_allowed allowed, notReset, disabled]
  rfl

end AllowedStep

/-! ## Authored and structural correctness -/

namespace Description

open Naming Authoring.CircuitDescription

/--
Elaborating the `wire`/`assign` circuit in `EnabledResetRegister.lean` produces
the existing typed enabled-reset-register hierarchy, including its feedback
connection, without name collisions.

This is the checked translation from the reader-facing circuit to the
production structure. The separate `implements_contract` theorem below states
that the structure satisfies the cycle contract.
-/
theorem authored_definition_corresponds (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Corresponds (description signalType resetValue)
      (EnabledResetRegister.naming signalType resetValue) :=
  Internal.corresponds signalType resetValue

end Description

/-- The concrete enabled-reset-register structure implements its cycle
contract at the shared step boundary. -/
theorem implements_contract (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Implements
      (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue)
      (certification signalType resetValue).stateCorresponds :=

    (certification signalType resetValue).implements

end Silean.Modules.EnabledResetRegister
