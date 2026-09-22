import Silean.Modules.AddWithCarry.AddWithCarry

assert_not_imported Silean.Modules.AddWithCarry.Internal.AddWithCarryStructure
assert_not_imported Silean.Modules.AddWithCarry.Internal.AddWithCarryVerification

namespace SileanTests.AddWithCarryAuthoring

open Silean

#check Modules.AddWithCarry.cycleContract
#check ∀ (width : Nat) {step : (Modules.AddWithCarry.cycleContract width).Step},
  (Modules.AddWithCarry.cycleContract width).Allows step →
    BitVector.toNat width (step.outputs .result) +
        2 ^ width * (step.outputs .carryOut).toNat =
      BitVector.toNat width (step.inputs .left) +
        BitVector.toNat width (step.inputs .right) +
          (step.inputs .carryIn).toNat

end SileanTests.AddWithCarryAuthoring
