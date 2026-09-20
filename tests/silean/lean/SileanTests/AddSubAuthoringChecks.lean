import Silean.Modules.AddSub.AddSub

assert_not_imported Silean.Modules.AddSub.Internal.AddSubArithmetic
assert_not_imported Silean.Modules.AddSub.Internal.AddSubStructure
assert_not_imported Silean.Modules.AddSub.Internal.AddSubVerification

namespace SileanTests.AddSubAuthoring

open Silean
open Silean.Authoring.CircuitDescription.Description

#check ∀ (width : Nat),
  (Modules.AddSub.description width).ImplementsCycleContract
    (Modules.AddSub.cycleContract width) (Modules.AddSub.Naming.ports width)

#check ∀ (width : Nat) {step : (Modules.AddSub.cycleContract width).Step},
  (Modules.AddSub.cycleContract width).Allows step →
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

end SileanTests.AddSubAuthoring
