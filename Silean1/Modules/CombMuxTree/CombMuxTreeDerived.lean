import Silean.Modules.CombMuxTree.Internal.CombMuxTreeVerification

/-! Public mux-tree declarations backed by the recursive implementation. -/

namespace Silean.Modules.CombMuxTree

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (values : Net (.vector (BinaryToOneHot.size indexWidth) element))
    (index : Net (.vector indexWidth .bit)) : Builder (Net element) := do
  let outputs ← ports.placeNamed element indexWidth name
    (moduleStructure element indexWidth) (Naming.naming element indexWidth)
    values index
  pure outputs.result

noncomputable def place
    (values : Net (.vector (BinaryToOneHot.size indexWidth) element))
    (index : Net (.vector indexWidth .bit)) : Builder (Net element) := do
  let outputs ← ports.placeIndexed element indexWidth "comb_mux_tree"
    (moduleStructure element indexWidth) (Naming.naming element indexWidth)
    values index
  pure outputs.result

attribute [circuit_description] placeNamed place

/-- Every realizable step selects the value named by the index bits. -/
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
  exact cycleContract.result element indexWidth allowed

/-- The recursive mux tree implements its exact selection contract. -/
theorem implements_contract (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element indexWidth)
      (cycleContract element indexWidth)
      (certification element indexWidth).stateCorresponds :=
  (certification element indexWidth).implements

end Silean.Modules.CombMuxTree
