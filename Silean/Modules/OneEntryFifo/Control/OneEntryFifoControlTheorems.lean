import Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlVerification

/-! # One-entry FIFO control theorems

These are the small interface used by the parent FIFO proof. The gate-level
structure and certification are private implementation details.
-/

namespace Silean.Modules.OneEntryFifo.Control

open Silean

section AllowedStep

variable {step : cycleContract.Step}
  (allowed : cycleContract.Allows step)

include allowed

/-- The producer may send when storage is empty or the consumer is ready. -/
theorem upstreamReady_of_allowed :
    step.outputs .upstreamReady =
      (step.inputs .downstreamReady || !step.inputs .storedValid) :=
  (controlRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .control) |>.1

/-- Storage changes exactly when readiness agrees with current occupancy. -/
theorem storageUpdate_of_allowed :
    step.outputs .storageUpdate =
      ((step.inputs .downstreamReady && step.inputs .storedValid) ||
        (!step.inputs .downstreamReady && !step.inputs .storedValid)) :=
  (controlRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .control) |>.2

end AllowedStep

namespace Description

open Naming Authoring.CircuitDescription

/-- The readable gate-level circuit elaborates to the typed control child used
by the parent FIFO. -/
theorem authored_definition_corresponds :
    Corresponds description Control.naming :=
  Internal.corresponds

end Description

/-- The concrete control hierarchy implements its exact combinational
contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.OneEntryFifo.Control
