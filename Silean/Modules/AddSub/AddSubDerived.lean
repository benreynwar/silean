import Silean.Modules.AddSub.Internal.AddSubVerification

/-! Public add/subtract declarations backed by the authored construction and
generated structural proofs. -/

namespace Silean.Modules.AddSub

open Silean
open Authoring.CircuitDescription

/-- Place an add/subtract unit using the next conventional indexed name. -/
noncomputable def place (left right : Net (.vector width .bit))
    (subtract : Net .bit) : Builder (ports.OutputNets width) :=
  ports.placeIndexed width "add_sub" (moduleStructure width)
    (naming width) left right subtract

attribute [circuit_description] place

/-- The result is addition or modular subtraction according to `subtract`. -/
theorem addSubBits_result_toNat (width : Nat)
    (left right : Fin width → Bool) (subtract : Bool) :
    BitVector.toNat width (addSubBits width left right subtract).1 =
      if subtract then
        (BitVector.toNat width left + BitVector.cardinality width -
          BitVector.toNat width right) % BitVector.cardinality width
      else
        (BitVector.toNat width left + BitVector.toNat width right) %
          BitVector.cardinality width :=
  Internal.addSubBits_result_toNat width left right subtract

/-- In subtraction mode carry-out is the conventional no-borrow flag. -/
theorem addSubBits_carry_subtract (width : Nat)
    (left right : Fin width → Bool) :
    (addSubBits width left right true).2 =
      decide (BitVector.toNat width right ≤ BitVector.toNat width left) :=
  Internal.addSubBits_carry_subtract width left right

/-- An allowed step's result has the expected arithmetic value. -/
theorem result_toNat_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toNat width (step.outputs .result) =
      bif step.inputs .subtract then
        (BitVector.toNat width (step.inputs .left) +
          BitVector.cardinality width -
          BitVector.toNat width (step.inputs .right)) %
            BitVector.cardinality width
      else
        (BitVector.toNat width (step.inputs .left) +
          BitVector.toNat width (step.inputs .right)) %
            BitVector.cardinality width := by
  rw [cycleContract.result width allowed]
  have result := addSubBits_result_toNat width
    (step.inputs .left) (step.inputs .right) (step.inputs .subtract)
  cases subtract : step.inputs .subtract <;>
    simp [subtract] at result ⊢ <;> exact result

/-- In subtraction mode, carry-out is true exactly when no borrow occurred. -/
theorem carry_eq_noBorrow_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step)
    (subtracts : step.inputs .subtract = true) :
    step.outputs .carryOut =
      decide (BitVector.toNat width (step.inputs .right) ≤
        BitVector.toNat width (step.inputs .left)) := by
  rw [cycleContract.carryOut width allowed]
  change (addSubBits width (step.inputs .left) (step.inputs .right)
    (step.inputs .subtract)).2 = _
  rw [subtracts]
  exact addSubBits_carry_subtract width
    (step.inputs .left) (step.inputs .right)

/-- Every typed implementation corresponding to the authored construction
implements its cycle contract. -/
theorem construction_correct (width : Nat) :
    (description width).ImplementsCycleContract (cycleContract width)
      (Naming.ports width) :=
  Internal.construction_correct width

/-- The generated structural add/subtract unit implements the cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.AddSub
