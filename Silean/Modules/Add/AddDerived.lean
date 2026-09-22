import Silean.Modules.Add.Internal.AddVerification
import Silean.Modules.Arithmetic.Internal.SignedExtendedBounds

/-! Public placement and correctness declarations for structural addition. -/

namespace Silean.Modules.Add

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit)) := do
  let outputs ← ports.placeNamed leftWidth rightWidth leftSigned rightSigned
    extendOutput name
    (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming leftWidth rightWidth leftSigned rightSigned extendOutput) left right
  pure outputs.result

noncomputable def place
    (leftSigned rightSigned extendOutput : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit)) := do
  let outputs ← ports.placeIndexed leftWidth rightWidth leftSigned rightSigned
    extendOutput "add"
    (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming leftWidth rightWidth leftSigned rightSigned extendOutput) left right
  pure outputs.result

attribute [circuit_description] placeNamed place

theorem result_of_realization (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    {step : (moduleStructure leftWidth rightWidth leftSigned rightSigned
      extendOutput).Step}
    (realizes : (moduleStructure leftWidth rightWidth leftSigned rightSigned
      extendOutput).Realizes step) :
    step.outputs .result = resultValue leftWidth rightWidth leftSigned
      rightSigned extendOutput (step.inputs .left) (step.inputs .right) := by
  obtain ⟨_, _, allowed⟩ := allowed_of_realization leftWidth rightWidth
    leftSigned rightSigned extendOutput realizes
  exact cycleContract.result leftWidth rightWidth leftSigned rightSigned
    extendOutput allowed

theorem implements_contract (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool) :
    Contracts.Cycle.Implements
      (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
      (cycleContract leftWidth rightWidth leftSigned rightSigned extendOutput)
      (certification leftWidth rightWidth leftSigned rightSigned
        extendOutput).stateCorresponds :=
  (certification leftWidth rightWidth leftSigned rightSigned
    extendOutput).implements

/-- One-bit-extended equal-width signed addition preserves the exact integer
sum rather than wrapping it. -/
theorem resultValue_toInt_signed_extended (width : Nat)
    (left right : Fin width → Bool) :
    (BitVector.toBitVec (Arithmetic.resultWidth width width true)
      (resultValue width width true true true left right)).toInt =
      (BitVector.toBitVec width left).toInt +
        (BitVector.toBitVec width right).toInt := by
  rw [resultValue, Arithmetic.encode, BitVector.toBitVec_ofBitVec]
  simp only [Arithmetic.operandValue, if_true]
  apply BitVec.toInt_ofInt_eq_self
  · simp [Arithmetic.resultWidth]
  · simpa [Arithmetic.resultWidth] using
      (Arithmetic.Internal.signed_add_bounds_extended width
        (BitVector.toBitVec width left) (BitVector.toBitVec width right)).1
  · simpa [Arithmetic.resultWidth] using
      (Arithmetic.Internal.signed_add_bounds_extended width
        (BitVector.toBitVec width left) (BitVector.toBitVec width right)).2

end Silean.Modules.Add
