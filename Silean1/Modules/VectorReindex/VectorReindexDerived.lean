import Silean.Modules.VectorReindex.Internal.VectorReindexVerification

/-! Public vector-reindex declarations backed by generated internals. -/

namespace Silean.Modules.VectorReindex

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (element : SignalType) (layout : Fin outputWidth → Fin inputWidth)
    (input : Net (.vector inputWidth element)) :
    Builder (Net (.vector outputWidth element)) := do
  let outputs ← ports.placeNamed element inputWidth outputWidth name
    (moduleStructure element inputWidth outputWidth layout)
    (naming element inputWidth outputWidth layout) input
  pure outputs.output

noncomputable def place (element : SignalType)
    (layout : Fin outputWidth → Fin inputWidth)
    (input : Net (.vector inputWidth element)) :
    Builder (Net (.vector outputWidth element)) := do
  let outputs ← ports.placeIndexed element inputWidth outputWidth
    "vector_reindex" (moduleStructure element inputWidth outputWidth layout)
    (naming element inputWidth outputWidth layout) input
  pure outputs.output

attribute [circuit_description] placeNamed place

theorem output_of_realization (element : SignalType)
    (inputWidth outputWidth : Nat) (layout : Fin outputWidth → Fin inputWidth)
    {step : (moduleStructure element inputWidth outputWidth layout).Step}
    (realizes :
      (moduleStructure element inputWidth outputWidth layout).Realizes step) :
    step.outputs .output =
      VectorReindex.apply layout (step.inputs .input) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element inputWidth outputWidth layout).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element inputWidth outputWidth layout).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.output element inputWidth outputWidth layout allowed

theorem implements_contract (element : SignalType)
    (inputWidth outputWidth : Nat) (layout : Fin outputWidth → Fin inputWidth) :
    Contracts.Cycle.Implements
      (moduleStructure element inputWidth outputWidth layout)
      (cycleContract element inputWidth outputWidth layout)
      (certification element inputWidth outputWidth layout).stateCorresponds :=
  (certification element inputWidth outputWidth layout).implements

end Silean.Modules.VectorReindex
