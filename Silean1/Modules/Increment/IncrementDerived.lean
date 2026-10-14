import Silean.Modules.Increment.Internal.IncrementArithmetic
import Silean.Modules.Increment.Internal.IncrementVerification

/-! Public incrementer declarations backed by the recursive implementation. -/

namespace Silean.Modules.Increment

open Silean
open Authoring.CircuitDescription

/-- Place an incrementer under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (value : Net (.vector width .bit)) : Builder (ports.OutputNets width) :=
  ports.placeNamed width name (moduleStructure width) (Naming.naming width) value

/-- Place an incrementer using the next conventional indexed name. -/
noncomputable def place (value : Net (.vector width .bit)) :
    Builder (ports.OutputNets width) :=
  ports.placeIndexed width "increment" (moduleStructure width)
    (Naming.naming width) value

attribute [circuit_description] placeNamed place

/-- Incrementing adds one modulo the vector width. -/
theorem incrementValue_toNat (width : Nat) (bits : Fin width → Bool) :
    BitVector.toNat width (incrementValue width bits) =
      (BitVector.toNat width bits + 1) % BitVector.cardinality width :=
  Internal.incrementValue_toNat width bits

/-- Numerically, an allowed step adds one modulo the vector width. -/
theorem result_toNat_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toNat width (step.outputs .result) =
      (BitVector.toNat width (step.inputs .value) + 1) %
        BitVector.cardinality width := by
  rw [cycleContract.result width allowed]
  exact incrementValue_toNat width (step.inputs .value)

/-- Every realizable incrementer step returns the mathematical increment. -/
theorem result_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    step.outputs .result = incrementValue width (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact cycleContract.result width allowed

/-- The recursive incrementer implements its exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.Increment
