import Silean.Modules.VectorSlice.Internal.VectorSliceVerification

/-! Public vector-slice declarations backed by generated internals. -/

namespace Silean.Modules.VectorSlice

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (element : SignalType) (prefixWidth width suffixWidth : Nat)
    (value : Net (.vector (prefixWidth + width + suffixWidth) element)) :
    Builder (Net (.vector width element)) := do
  let outputs ← ports.placeNamed element prefixWidth width suffixWidth name
    (moduleStructure element prefixWidth width suffixWidth)
    (naming element prefixWidth width suffixWidth) value
  pure outputs.result

noncomputable def place (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (value : Net (.vector (prefixWidth + width + suffixWidth) element)) :
    Builder (Net (.vector width element)) := do
  let outputs ← ports.placeIndexed element prefixWidth width suffixWidth
    "vector_slice" (moduleStructure element prefixWidth width suffixWidth)
    (naming element prefixWidth width suffixWidth) value
  pure outputs.result

attribute [circuit_description] placeNamed place

/-- Every realizable step returns the requested contiguous range. -/
theorem result_of_realization (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    {step : (moduleStructure element prefixWidth width suffixWidth).Step}
    (realizes :
      (moduleStructure element prefixWidth width suffixWidth).Realizes step) :
    step.outputs .result = slice (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element prefixWidth width suffixWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element prefixWidth width suffixWidth).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.result element prefixWidth width suffixWidth allowed

/-- The generated hierarchy implements the exact slice contract. -/
theorem implements_contract (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth)
      (certification element prefixWidth width suffixWidth).stateCorresponds :=
  (certification element prefixWidth width suffixWidth).implements

end Silean.Modules.VectorSlice
