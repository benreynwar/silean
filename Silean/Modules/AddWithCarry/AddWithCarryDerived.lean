import Silean.Modules.AddWithCarry.Internal.AddWithCarryVerification
import Silean.Authoring.ModuleCycleCertification

/-! Public adder declarations backed by the recursive implementation. -/

namespace Silean.Modules.AddWithCarry

open Silean
open Authoring.CircuitDescription

/-- Place a fixed-width adder using the next conventional indexed name. -/
noncomputable def place (left right : Net (.vector width .bit))
    (carryIn : Net .bit) : Builder (ports.OutputNets width) :=
  ports.placeIndexed width "add_with_carry" (moduleStructure width)
    (Naming.naming width) left right carryIn

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

/-- With no incoming carry, packing the result is native fixed-width
addition. -/
theorem toBitVec_resultValue_noCarry (width : Nat)
    (left right : Fin width → Bool) :
    BitVector.toBitVec width (resultValue width left right false) =
      BitVector.toBitVec width left + BitVector.toBitVec width right := by
  rw [resultValue, totalValue]
  simp only [Bool.toNat_false, Nat.add_zero, BitVector.toBitVec_ofNat]
  simpa only [BitVector.toBitVec] using
    (BitVec.ofNat_add (n := width) (BitVector.toNat width left)
      (BitVector.toNat width right))

/-- The recursive ripple implementation satisfies the exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.AddWithCarry
