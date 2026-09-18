import Silean.Modules.OneEntryFifo.Internal.OneEntryFifoVerification

/-! # One-entry FIFO cycle theorems

These theorems expose the exact behavior of one clock cycle. They intentionally
do not state the higher-level queue contract; that abstraction and its
refinement proof live in `OneEntryFifoFifoTheorems.lean`.
-/

namespace Silean.Modules.OneEntryFifo

open Silean

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- Output valid is asserted for either a buffered or incoming payload. -/
theorem outputValid_of_allowed :
    step.outputs .outputValid =
      (step.currentState .storedValid || step.inputs .inputValid) :=
  (forwardRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward) |>.1

/-- A buffered payload has priority; otherwise the input falls through. -/
theorem outputData_of_allowed :
    step.outputs .outputData =
      bif step.currentState .storedValid then step.currentState .storedData
      else step.inputs .inputData :=
  (forwardRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward) |>.2

/-- The producer may send when the entry is empty or the consumer is ready. -/
theorem inputReady_of_allowed :
    step.outputs .inputReady =
      (step.inputs .outputReady || !step.currentState .storedValid) :=
  (readyRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .ready)

/-- The complete next occupancy equation, including synchronous reset. -/
theorem next_storedValid_of_allowed :
    step.nextState .storedValid =
      bif step.inputs .reset then false else
        bif ((step.inputs .outputReady && step.currentState .storedValid) ||
          (!step.inputs .outputReady && !step.currentState .storedValid))
          then step.inputs .inputValid else step.currentState .storedValid := by
  rw [allowed.2]
  rfl

/-- Payload storage follows the ordinary update condition. Reset clears valid
but does not require choosing or writing a reset payload. -/
theorem next_storedData_of_allowed :
    step.nextState .storedData =
      bif ((step.inputs .outputReady && step.currentState .storedValid) ||
        (!step.inputs .outputReady && !step.currentState .storedValid))
        then step.inputs .inputData else step.currentState .storedData := by
  rw [allowed.2]
  rfl

/-- Reset empties the FIFO regardless of the handshake inputs. -/
theorem next_storedValid_of_reset (reset : step.inputs .reset = true) :
    step.nextState .storedValid = false := by
  rw [next_storedValid_of_allowed allowed, reset]
  rfl

/-- Without an update, the buffered payload is retained. -/
theorem next_storedData_of_no_update
    (noUpdate : ((step.inputs .outputReady && step.currentState .storedValid) ||
      (!step.inputs .outputReady && !step.currentState .storedValid)) = false) :
    step.nextState .storedData = step.currentState .storedData := by
  rw [next_storedData_of_allowed allowed, noUpdate]
  rfl

end AllowedStep

namespace Description

open Naming Authoring.CircuitDescription

/-- Elaborating the readable feedback circuit in `OneEntryFifo.lean` produces
exactly the typed hierarchy used by verification and emission. -/
theorem authored_definition_corresponds (signalType : SignalType) :
    Corresponds (description signalType) (OneEntryFifo.naming signalType) :=
  Internal.corresponds signalType

end Description

/-- The concrete one-entry FIFO hierarchy implements its exact cycle contract
at the shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=

    (certification signalType).implements

end Silean.Modules.OneEntryFifo
