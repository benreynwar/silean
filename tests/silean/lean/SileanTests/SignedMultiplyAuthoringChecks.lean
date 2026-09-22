import Silean.Modules.SignedMultiply.SignedMultiply

assert_not_imported Silean.Modules.SignedMultiply.Internal.SignedMultiplyArithmetic
assert_not_imported Silean.Modules.SignedMultiply.Internal.SignedMultiplyStructure
assert_not_imported Silean.Modules.SignedMultiply.Internal.SignedMultiplyVerification

namespace SileanTests.SignedMultiplyAuthoring

open Silean
open Silean.Authoring.CircuitDescription.Description

#check ∀ (leftWidth rightWidth : Nat),
  (Modules.SignedMultiply.description leftWidth rightWidth).ImplementsCycleContract
    (Modules.SignedMultiply.cycleContract leftWidth rightWidth)
    (Modules.SignedMultiply.Naming.ports leftWidth rightWidth)

#check ∀ (leftWidth rightWidth : Nat)
    {step : (Modules.SignedMultiply.cycleContract leftWidth rightWidth).Step},
  (Modules.SignedMultiply.cycleContract leftWidth rightWidth).Allows step →
    (BitVector.toBitVec (leftWidth + rightWidth)
      (step.outputs .result)).toInt =
      (BitVector.toBitVec leftWidth (step.inputs .left)).toInt *
        (BitVector.toBitVec rightWidth (step.inputs .right)).toInt

end SileanTests.SignedMultiplyAuthoring
