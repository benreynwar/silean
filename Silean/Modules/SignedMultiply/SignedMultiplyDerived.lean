import Silean.Modules.SignedMultiply.Internal.SignedMultiplyVerification

/-! Public signed-multiplier declarations backed by the authored construction
and generated structural proof. -/

namespace Silean.Modules.SignedMultiply

open Silean
open Authoring.CircuitDescription

/-- Place a full-width signed multiplier using the next conventional indexed
name. -/
noncomputable def place
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (ports.OutputNets leftWidth rightWidth) :=
  ports.placeIndexed leftWidth rightWidth "signed_multiply"
    (moduleStructure leftWidth rightWidth)
    (naming leftWidth rightWidth) left right

attribute [circuit_description] place

/-- The product of independently sized signed vectors fits exactly in their
combined signed width. -/
theorem product_bounds (leftWidth rightWidth : Nat)
    (left : BitVec leftWidth) (right : BitVec rightWidth) :
    -2 ^ (leftWidth + rightWidth - 1) ≤ left.toInt * right.toInt ∧
      left.toInt * right.toInt < 2 ^ (leftWidth + rightWidth - 1) :=
  Internal.product_bounds leftWidth rightWidth left right

/-- Decoding the pure contract result gives exact integer multiplication. -/
theorem resultValue_toInt (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (resultValue leftWidth rightWidth left right)).toInt =
      (BitVector.toBitVec leftWidth left).toInt *
        (BitVector.toBitVec rightWidth right).toInt :=
  Internal.resultValue_toInt leftWidth rightWidth left right

/-- An allowed signed-multiplier step computes the exact mathematical integer
product, with no truncation or wraparound. -/
theorem result_toInt_of_allowed (leftWidth rightWidth : Nat)
    {step : (cycleContract leftWidth rightWidth).Step}
    (allowed : (cycleContract leftWidth rightWidth).Allows step) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (step.outputs .result)).toInt =
      (BitVector.toBitVec leftWidth (step.inputs .left)).toInt *
        (BitVector.toBitVec rightWidth (step.inputs .right)).toInt := by
  rw [cycleContract.result leftWidth rightWidth allowed]
  exact resultValue_toInt leftWidth rightWidth
    (step.inputs .left) (step.inputs .right)

/-- Every typed implementation corresponding to the authored construction
implements the signed-multiplication contract. -/
theorem construction_correct (leftWidth rightWidth : Nat) :
    (description leftWidth rightWidth).ImplementsCycleContract
      (cycleContract leftWidth rightWidth)
      (Naming.ports leftWidth rightWidth) :=
  Internal.construction_correct leftWidth rightWidth

/-- The generated structural signed multiplier implements its cycle
contract. -/
theorem implements_contract (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure leftWidth rightWidth)
      (cycleContract leftWidth rightWidth)
      (certification leftWidth rightWidth).stateCorresponds :=
  (certification leftWidth rightWidth).implements

/-- Every structural realization computes the exact signed integer product. -/
theorem result_toInt_of_realization (leftWidth rightWidth : Nat)
    {step : (moduleStructure leftWidth rightWidth).Step}
    (realizes : (moduleStructure leftWidth rightWidth).Realizes step) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (step.outputs .result)).toInt =
      (BitVector.toBitVec leftWidth (step.inputs .left)).toInt *
        (BitVector.toBitVec rightWidth (step.inputs .right)).toInt := by
  obtain ⟨_, _, allowed⟩ :=
    allowed_of_realization leftWidth rightWidth realizes
  exact result_toInt_of_allowed leftWidth rightWidth allowed

end Silean.Modules.SignedMultiply
