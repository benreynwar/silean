import Silean.Modules.ResetRegister.Internal.ResetRegisterVerification

/-! # Reset-register theorems

This file is the supported proof interface for `ResetRegister`. Its theorems
describe complete boundary steps; the hierarchy assignment and structural
state relation used to establish them remain under `Internal/`.
-/

namespace Silean.Modules.ResetRegister

open Silean

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

/-- The next stored value is the fixed reset value when reset is high and the
ordinary input otherwise. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .reset then resetValue else step.inputs .value := by
  rw [allowed.2]
  rfl

/-- Reset determines the next stored value. -/
theorem next_stored_of_reset (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, reset]
  rfl

/-- With reset low, the ordinary input becomes the next stored value. -/
theorem next_stored_of_not_reset (notReset : step.inputs .reset = false) :
    step.nextState .stored = step.inputs .value := by
  rw [next_stored_of_allowed allowed, notReset]
  rfl

end AllowedStep

namespace Description

open Naming Authoring.CircuitDescription

/-- Elaborating the readable circuit in `ResetRegister.lean` produces exactly
the typed reset-register hierarchy used by verification and emission. -/
theorem authored_definition_corresponds (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Corresponds (description signalType resetValue)
      (ResetRegister.naming signalType resetValue) :=
  Internal.corresponds signalType resetValue

end Description

/-- The concrete reset-register hierarchy implements its exact cycle
contract at the shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Implements
      (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue)
      (certification signalType resetValue).stateCorresponds :=

    (certification signalType resetValue).implements

end Silean.Modules.ResetRegister
