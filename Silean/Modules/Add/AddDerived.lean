import Silean.Modules.Add.Internal.AddVerification

/-! Public adder declarations backed by the recursive implementation. -/

namespace Silean.Modules.Add

open Silean
open Authoring.CircuitDescription

/-- Place a fixed-width adder using the next conventional indexed name. -/
noncomputable def place (left right : Net (.vector width .bit))
    (carryIn : Net .bit) : Builder (ports.OutputNets width) :=
  ports.placeIndexed width "add" (moduleStructure width) (Naming.naming width)
    left right carryIn

attribute [circuit_description] place

/-- The result and carry bit encode the complete natural-number sum. -/
theorem addBits_numeric (width : Nat) (left right : Fin width → Bool)
    (carry : Bool) :
    BitVector.toNat width (addBits width left right carry).1 +
        BitVector.cardinality width * (addBits width left right carry).2.toNat =
      BitVector.toNat width left + BitVector.toNat width right + carry.toNat :=
  Internal.addBits_numeric width left right carry

/-- Numerically, an allowed adder step produces the full sum across its result
vector and carry-out bit. -/
theorem numeric_value_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toNat width (step.outputs .result) +
        2 ^ width * (step.outputs .carryOut).toNat =
      BitVector.toNat width (step.inputs .left) +
        BitVector.toNat width (step.inputs .right) +
          (step.inputs .carryIn).toNat := by
  rw [cycleContract.result width allowed, cycleContract.carryOut width allowed,
    ← BitVector.cardinality_eq_pow]
  exact addBits_numeric width (step.inputs .left) (step.inputs .right)
    (step.inputs .carryIn)

/-- The recursive ripple implementation satisfies the exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.Add
