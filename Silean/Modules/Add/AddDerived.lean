import Silean.Modules.Add.Internal.AddVerification
import Silean.Authoring.ModuleCycleCertification

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

module_cycle_realization_bridge allowed_of_realization (width : Nat)
  for moduleStructure width implementing cycleContract width using certification

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
  simpa [totalValue] using Internal.naturalValues_numeric width
    (step.inputs .left) (step.inputs .right) (step.inputs .carryIn)

/-- The result vector is the low `width` bits of the ordinary input sum. -/
theorem result_toNat_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toNat width (step.outputs .result) =
      totalValue width (step.inputs .left) (step.inputs .right)
        (step.inputs .carryIn) % BitVector.cardinality width := by
  rw [cycleContract.result width allowed]
  change BitVector.toNat width
      (resultValue width (step.inputs .left) (step.inputs .right)
        (step.inputs .carryIn)) = _
  rw [resultValue, BitVector.toNat_ofNat]

/-- The recursive ripple implementation satisfies the exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.Add
