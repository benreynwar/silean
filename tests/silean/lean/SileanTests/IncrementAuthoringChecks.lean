import Silean.Modules.Increment.Increment

assert_not_imported Silean.Modules.Increment.Internal.IncrementArithmetic
assert_not_imported Silean.Modules.Increment.Internal.IncrementStructure
assert_not_imported Silean.Modules.Increment.Internal.IncrementVerification

namespace SileanTests.IncrementAuthoring

open Silean

#check Modules.Increment.cycleContract
#check ∀ (width : Nat) {step : (Modules.Increment.cycleContract width).Step},
  (Modules.Increment.cycleContract width).Allows step →
    BitVector.toNat width (step.outputs .result) =
      (BitVector.toNat width (step.inputs .value) + 1) %
        BitVector.cardinality width

end SileanTests.IncrementAuthoring
