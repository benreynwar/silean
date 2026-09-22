import Silean.Modules.AddSubWithCarry.AddSubWithCarry

assert_not_imported Silean.Modules.AddSubWithCarry.Internal.AddSubWithCarryArithmetic
assert_not_imported Silean.Modules.AddSubWithCarry.Internal.AddSubWithCarryStructure
assert_not_imported Silean.Modules.AddSubWithCarry.Internal.AddSubWithCarryVerification

namespace SileanTests.AddSubWithCarryAuthoring

open Silean
open Silean.Authoring.CircuitDescription.Description

#check ∀ (width : Nat),
  (Modules.AddSubWithCarry.description width).ImplementsCycleContract
    (Modules.AddSubWithCarry.cycleContract width)
      (Modules.AddSubWithCarry.Naming.ports width)

#check ∀ (width : Nat)
    {step : (Modules.AddSubWithCarry.cycleContract width).Step},
  (Modules.AddSubWithCarry.cycleContract width).Allows step →
    BitVector.toNat width (step.outputs .result) =
      bif step.inputs .subtract then
        (BitVector.toNat width (step.inputs .left) +
          BitVector.cardinality width -
          BitVector.toNat width (step.inputs .right)) %
            BitVector.cardinality width
      else
        (BitVector.toNat width (step.inputs .left) +
          BitVector.toNat width (step.inputs .right)) %
            BitVector.cardinality width

end SileanTests.AddSubWithCarryAuthoring
