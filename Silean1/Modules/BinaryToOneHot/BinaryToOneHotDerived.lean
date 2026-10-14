import Silean.Modules.BinaryToOneHot.Internal.BinaryToOneHotVerification

/-! Public decoder declarations backed by the recursive implementation. -/

namespace Silean.Modules.BinaryToOneHot

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName) (width : Nat)
    (value : Net (.vector width .bit)) :
    Builder (Net (.vector (size width) .bit)) := do
  let outputs ← ports.placeNamed width name (moduleStructure width)
    (Naming.naming width) value
  pure outputs.result

noncomputable def place (width : Nat) (value : Net (.vector width .bit)) :
    Builder (Net (.vector (size width) .bit)) := do
  let outputs ← ports.placeIndexed width "binary_to_one_hot"
    (moduleStructure width) (Naming.naming width) value
  pure outputs.result

attribute [circuit_description] placeNamed place

/-- Every realizable step produces the one-hot decoding of its input. -/
theorem result_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    step.outputs .result = oneHot width (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact cycleContract.result width allowed

/-- The recursive decoder implements its exact one-hot contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.BinaryToOneHot
