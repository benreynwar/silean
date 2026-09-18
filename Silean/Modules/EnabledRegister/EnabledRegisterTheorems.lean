import Silean.Modules.EnabledRegister.Internal.EnabledRegisterVerification

/-! # Enabled-register theorems

The public interface describes complete boundary steps. Hierarchy assignments,
schedules, and the representation relation for the nested register remain in
`Internal/`.
-/

namespace Silean.Modules.EnabledRegister

open Silean

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- An allowed step exposes the value stored before the clock edge. -/
theorem q_of_allowed : step.outputs .q = step.currentState .stored :=
  (observeRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- Enable chooses between loading new data and retaining the stored value. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .enable then step.inputs .data
      else step.currentState .stored := by
  rw [allowed.2]
  rfl

/-- With enable high, the input becomes the next stored value. -/
theorem next_stored_of_enabled (enabled : step.inputs .enable = true) :
    step.nextState .stored = step.inputs .data := by
  rw [next_stored_of_allowed allowed, enabled]
  rfl

/-- With enable low, the current stored value is retained. -/
theorem next_stored_of_disabled (disabled : step.inputs .enable = false) :
    step.nextState .stored = step.currentState .stored := by
  rw [next_stored_of_allowed allowed, disabled]
  rfl

end AllowedStep

namespace Description

open Naming Authoring.CircuitDescription

/-- Elaborating the readable feedback circuit in `EnabledRegister.lean`
produces exactly the typed hierarchy used by verification and emission. -/
theorem authored_definition_corresponds (signalType : SignalType) :
    Corresponds (description signalType) (EnabledRegister.naming signalType) :=
  Internal.corresponds signalType

end Description

/-- The concrete enabled-register hierarchy implements its exact cycle
contract at the shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=

    (certification signalType).implements

end Silean.Modules.EnabledRegister
