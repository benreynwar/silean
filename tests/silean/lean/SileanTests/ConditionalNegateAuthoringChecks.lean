import Silean.Modules.ConditionalNegate.ConditionalNegate

assert_not_imported Silean.Modules.ConditionalNegate.Internal.ConditionalNegateArithmetic
assert_not_imported Silean.Modules.ConditionalNegate.Internal.ConditionalNegateStructure
assert_not_imported Silean.Modules.ConditionalNegate.Internal.ConditionalNegateVerification

namespace SileanTests.ConditionalNegateAuthoring

open Silean
open Silean.Authoring.CircuitDescription.Description

#check ∀ (width : Nat),
  (Modules.ConditionalNegate.description width).ImplementsCycleContract
    (Modules.ConditionalNegate.cycleContract width)
    (Modules.ConditionalNegate.Naming.ports width)

#check ∀ (width : Nat)
    {step : (Modules.ConditionalNegate.cycleContract width).Step},
  (Modules.ConditionalNegate.cycleContract width).Allows step →
    BitVector.toBitVec width (step.outputs .result) =
      bif step.inputs .negate then
        -BitVector.toBitVec width (step.inputs .value)
      else
        BitVector.toBitVec width (step.inputs .value)

end SileanTests.ConditionalNegateAuthoring
