import Silean.Modules.Fifo.Internal.FifoPointerControlVerification

/-! # FIFO pointer-control theorems

This is the supported structural proof interface. The thirteen-child gate and
adapter hierarchy and its rule schedules remain under `Internal/`.
-/

namespace Silean.Modules.Fifo.PointerControl

open Silean

/-- Every realizable pointer-control step has the complete combinational
behavior specified in `FifoPointerControl.lean`. -/
theorem behavior_of_realization (addressWidth : Nat)
    {step : (moduleStructure addressWidth).Step}
    (realizes : (moduleStructure addressWidth).Realizes step) :
    Behavior addressWidth step.inputs step.outputs := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification addressWidth).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification addressWidth).allows_of_realizes
    contractState step corresponds realizes
  exact Behavior.of_allowed addressWidth allowed

/-- The concrete pointer-control hierarchy implements its exact cycle
contract. -/
theorem implements_contract (addressWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure addressWidth)
      (cycleContract addressWidth)
      (certification addressWidth).stateCorresponds :=
  (certification addressWidth).implements

end Silean.Modules.Fifo.PointerControl
