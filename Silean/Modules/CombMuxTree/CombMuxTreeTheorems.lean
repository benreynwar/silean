import Silean.Modules.CombMuxTree.Internal.CombMuxTreeVerification

/-! # Combinational mux-tree theorems

The recursive hierarchy in `CombMuxTree.lean` implements its exact selection
contract. Its schedules and inductive certification remain internal. -/

namespace Silean.Modules.CombMuxTree

open Silean

/-- Every realizable boundary step selects the value named by the index bits. -/
theorem result_of_realization (element : SignalType) (indexWidth : Nat)
    {step : (moduleStructure element indexWidth).Step}
    (realizes : (moduleStructure element indexWidth).Realizes step) :
    step.outputs .result =
      select indexWidth (step.inputs .values) (step.inputs .index) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element indexWidth).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element indexWidth).allows_of_realizes
      contractState step corresponds realizes
  exact (outputRule_holds_iff element indexWidth step.inputs contractState
    step.outputs).mp (allowed.1 .apply)

theorem certified_moduleStructure (element : SignalType) (indexWidth : Nat) :
    (certified element indexWidth).moduleStructure =
      moduleStructure element indexWidth := rfl

theorem certified_cycleContract (element : SignalType) (indexWidth : Nat) :
    (certified element indexWidth).cycleContract =
      cycleContract element indexWidth := rfl

/-- The structural mux tree implements its exact selection contract. -/
theorem implements_contract (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element indexWidth)
      (cycleContract element indexWidth)
      (certification element indexWidth).stateCorresponds :=
  (certification element indexWidth).implements

end Silean.Modules.CombMuxTree
