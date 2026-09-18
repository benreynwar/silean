import Silean.Modules.BitMux.Internal.BitMuxVerification

/-! # Bit-mux theorems

This is the supported proof interface for the gate-level bit mux. Its primitive
children, schedule, and Boolean normalization remain internal details.
-/

namespace Silean.Modules.BitMux

open Silean

/-- Every realizable boundary step selects the requested input. -/
theorem result_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse := by
  obtain ⟨contractState, corresponds⟩ :=
    certification.hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    certification.allows_of_realizes contractState step corresponds realizes
  exact result_of_allowed allowed

/-- The gate-level hierarchy implements the exact mux cycle contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.BitMux
