import Silean.Modules.VectorSplit.Internal.VectorSplitVerification

/-! Public vector-split declarations backed by generated internals. -/

namespace Silean.Modules.VectorSplit

open Silean
open Authoring.CircuitDescription

/-- Place a vector split using the next conventional indexed name. -/
noncomputable def place (value : Net (.vector (leftWidth + rightWidth) element)) :
    Builder (ports.OutputNets element leftWidth rightWidth) :=
  ports.placeIndexed element leftWidth rightWidth "vector_split"
    (moduleStructure element leftWidth rightWidth)
    (naming element leftWidth rightWidth) value

attribute [circuit_description] place

/-- Every realizable step returns the two portions of its input. -/
theorem outputs_of_realization (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (moduleStructure element leftWidth rightWidth).Step}
    (realizes : (moduleStructure element leftWidth rightWidth).Realizes step) :
    step.outputs .left = leftPart (step.inputs .value) ∧
      step.outputs .right = rightPart (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element leftWidth rightWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element leftWidth rightWidth).allows_of_realizes
      contractState step corresponds realizes
  exact outputs_of_allowed element leftWidth rightWidth allowed

/-- The generated hierarchy implements the exact split contract. -/
theorem implements_contract (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth)
      (certification element leftWidth rightWidth).stateCorresponds :=
  (certification element leftWidth rightWidth).implements

end Silean.Modules.VectorSplit
