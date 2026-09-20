import Silean.Modules.Add.Add

assert_not_imported Silean.Modules.Add.Internal.AddStructure
assert_not_imported Silean.Modules.Add.Internal.AddVerification

namespace SileanTests.AddAuthoring

open Silean

#check Modules.Add.cycleContract
#check ∀ (width : Nat) {step : (Modules.Add.cycleContract width).Step},
  (Modules.Add.cycleContract width).Allows step →
    BitVector.toNat width (step.outputs .result) +
        2 ^ width * (step.outputs .carryOut).toNat =
      BitVector.toNat width (step.inputs .left) +
        BitVector.toNat width (step.inputs .right) +
          (step.inputs .carryIn).toNat

end SileanTests.AddAuthoring
