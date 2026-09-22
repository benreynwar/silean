import Silean.Modules.Add.AddDerived
import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyWidths
import Silean.Modules.SignedMultiply.SignedMultiplyDerived
import Silean.Modules.Sub.SubDerived

/-! Pure arithmetic bridge for the structural complex-product data path. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

open _root_.Silean
open _root_.Silean.Modules

def roundedNumeratorCircuitValue
    (leftWidth rightWidth discardedWidth : Nat)
    (numerator : Fin (numeratorWidth leftWidth rightWidth) → Bool) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  SignedRoundShift.resultValue
    (resultWidth leftWidth rightWidth discardedWidth)
    (effectiveDiscard leftWidth rightWidth discardedWidth)
    (VectorLayout.apply
      (roundInputLayout leftWidth rightWidth discardedWidth) numerator)

def roundedRealCircuitValue
    (leftWidth rightWidth discardedWidth : Nat)
    (realReal imagImag : Fin (productWidth leftWidth rightWidth) → Bool) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
    (Sub.resultValue
      (productWidth leftWidth rightWidth)
      (productWidth leftWidth rightWidth) true true true
      realReal imagImag)

def roundedImagCircuitValue
    (leftWidth rightWidth discardedWidth : Nat)
    (realImag imagReal : Fin (productWidth leftWidth rightWidth) → Bool) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
    (Add.resultValue
      (productWidth leftWidth rightWidth)
      (productWidth leftWidth rightWidth) true true true
      realImag imagReal)

theorem roundedRealCircuit_eq_resultValue
    (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) :
    roundedRealCircuitValue leftWidth rightWidth discardedWidth
        (SignedMultiply.resultValue leftWidth rightWidth leftReal rightReal)
        (SignedMultiply.resultValue leftWidth rightWidth leftImag rightImag) =
      realResultValue leftWidth rightWidth discardedWidth
        leftReal leftImag rightReal rightImag := by
  rw [roundedRealCircuitValue, roundedNumeratorCircuitValue,
    SignedRoundShift.resultValue]
  rw [toInt_apply_roundInputLayout]
  simp only [numeratorWidth, productWidth]
  rw [Sub.resultValue_toInt_signed_extended]
  rw [SignedMultiply.resultValue_toInt,
    SignedMultiply.resultValue_toInt]
  simpa [realResultValue, realNumerator, componentValue,
    Arithmetic.operandValue, Arithmetic.encode] using
    encode_roundNearestEven_effectiveDiscard
      leftWidth rightWidth discardedWidth
      ((BitVector.toBitVec leftWidth leftReal).toInt *
          (BitVector.toBitVec rightWidth rightReal).toInt -
        (BitVector.toBitVec leftWidth leftImag).toInt *
          (BitVector.toBitVec rightWidth rightImag).toInt)

theorem roundedImagCircuit_eq_resultValue
    (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) :
    roundedImagCircuitValue leftWidth rightWidth discardedWidth
        (SignedMultiply.resultValue leftWidth rightWidth leftReal rightImag)
        (SignedMultiply.resultValue leftWidth rightWidth leftImag rightReal) =
      imagResultValue leftWidth rightWidth discardedWidth
        leftReal leftImag rightReal rightImag := by
  rw [roundedImagCircuitValue, roundedNumeratorCircuitValue,
    SignedRoundShift.resultValue]
  rw [toInt_apply_roundInputLayout]
  simp only [numeratorWidth, productWidth]
  rw [Add.resultValue_toInt_signed_extended]
  rw [SignedMultiply.resultValue_toInt,
    SignedMultiply.resultValue_toInt]
  simpa [imagResultValue, imagNumerator, componentValue,
    Arithmetic.operandValue, Arithmetic.encode] using
    encode_roundNearestEven_effectiveDiscard
      leftWidth rightWidth discardedWidth
      ((BitVector.toBitVec leftWidth leftReal).toInt *
          (BitVector.toBitVec rightWidth rightImag).toInt +
        (BitVector.toBitVec leftWidth leftImag).toInt *
          (BitVector.toBitVec rightWidth rightReal).toInt)

end HTFFT.Silean.PipelinedSignedComplexMultiply.Internal
