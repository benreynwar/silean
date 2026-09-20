import Silean.Modules.VectorLayout.Internal.VectorLayoutVerification

/-! Public vector-layout declarations backed by generated internals. -/

namespace Silean.Modules.VectorLayout

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (layout : Fin outputWidth → BitSource inputWidth)
    (input : Net (.vector inputWidth .bit)) :
    Builder (Net (.vector outputWidth .bit)) := do
  let outputs ← ports.placeNamed inputWidth outputWidth name
    (moduleStructure inputWidth outputWidth layout)
    (naming inputWidth outputWidth layout) input
  pure outputs.output

noncomputable def place (layout : Fin outputWidth → BitSource inputWidth)
    (input : Net (.vector inputWidth .bit)) :
    Builder (Net (.vector outputWidth .bit)) := do
  let outputs ← ports.placeIndexed inputWidth outputWidth "vector_layout"
    (moduleStructure inputWidth outputWidth layout)
    (naming inputWidth outputWidth layout) input
  pure outputs.output

/-- Place a statically shifted, zero-extended vector layout. The emitted
instance uses a shift-specific name while retaining `VectorLayout` semantics. -/
noncomputable def placeWideningLeftShift (growthWidth : Nat)
    (shift : Fin (growthWidth + 1))
    (input : Net (.vector inputWidth .bit)) :
    Builder (Net (.vector (inputWidth + growthWidth) .bit)) := do
  let layout := wideningLeftShiftLayout inputWidth growthWidth shift
  let outputs ← ports.placeIndexed inputWidth (inputWidth + growthWidth)
    "left_shift" (moduleStructure inputWidth (inputWidth + growthWidth) layout)
    (naming inputWidth (inputWidth + growthWidth) layout) input
  pure outputs.output

attribute [circuit_description] placeNamed place placeWideningLeftShift

/-- Every realizable step applies the declared bit layout. -/
theorem output_of_realization (inputWidth outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    {step : (moduleStructure inputWidth outputWidth layout).Step}
    (realizes : (moduleStructure inputWidth outputWidth layout).Realizes step) :
    step.outputs .output = VectorLayout.apply layout (step.inputs .input) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification inputWidth outputWidth layout).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification inputWidth outputWidth layout).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.output inputWidth outputWidth layout allowed

/-- The generated hierarchy implements the exact layout contract. -/
theorem implements_contract (inputWidth outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth) :
    Contracts.Cycle.Implements (moduleStructure inputWidth outputWidth layout)
      (cycleContract inputWidth outputWidth layout)
      (certification inputWidth outputWidth layout).stateCorresponds :=
  (certification inputWidth outputWidth layout).implements

end Silean.Modules.VectorLayout
