import Silean.Modules.VectorConcat.Internal.VectorConcatVerification

/-! Public vector-concatenation declarations backed by generated internals. -/

namespace Silean.Modules.VectorConcat

open Silean
open Authoring.CircuitDescription

/-- Place a vector concatenation using the next conventional indexed name. -/
noncomputable def place (left : Net (.vector leftWidth element))
    (right : Net (.vector rightWidth element)) :
    Builder (Net (.vector (leftWidth + rightWidth) element)) := do
  let outputs ← ports.placeIndexed element leftWidth rightWidth "vector_concat"
    (moduleStructure element leftWidth rightWidth)
    (naming element leftWidth rightWidth) left right
  pure outputs.result

attribute [circuit_description] place

/-- Every realizable step concatenates the two input vectors. -/
theorem result_of_realization (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (moduleStructure element leftWidth rightWidth).Step}
    (realizes : (moduleStructure element leftWidth rightWidth).Realizes step) :
    step.outputs .result = concat (step.inputs .left) (step.inputs .right) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element leftWidth rightWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element leftWidth rightWidth).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.result element leftWidth rightWidth allowed

/-- The generated hierarchy implements the exact concatenation contract. -/
theorem implements_contract (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth)
      (certification element leftWidth rightWidth).stateCorresponds :=
  (certification element leftWidth rightWidth).implements

end Silean.Modules.VectorConcat
