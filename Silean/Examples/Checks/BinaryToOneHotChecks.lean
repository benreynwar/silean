import Silean.FIRRTL
import Silean.Modules.BinaryToOneHot

namespace Silean.Examples.Checks.BinaryToOneHot

open Silean Silean.FIRRTL

noncomputable example : ModuleCycleCertified
    (Modules.BinaryToOneHot.ports 0) := Modules.BinaryToOneHot.certified 0
noncomputable example : ModuleCycleCertified
    (Modules.BinaryToOneHot.ports 1) := Modules.BinaryToOneHot.certified 1
noncomputable example : ModuleCycleCertified
    (Modules.BinaryToOneHot.ports 2) := Modules.BinaryToOneHot.certified 2
noncomputable example : ModuleCycleCertified
    (Modules.BinaryToOneHot.ports 3) := Modules.BinaryToOneHot.certified 3

def inputs0 : (Modules.BinaryToOneHot.ports 0).inputs.Values
  | .value => fun index => Fin.elim0 index

def inputs1 : (Modules.BinaryToOneHot.ports 1).inputs.Values
  | .value => fun | 0 => true

def inputs2 : (Modules.BinaryToOneHot.ports 2).inputs.Values
  | .value => fun | 0 => true | 1 => false

def inputs3 : (Modules.BinaryToOneHot.ports 3).inputs.Values
  | .value => fun | 0 => true | 1 => true | 2 => false

def result (width : Nat) (inputs : (Modules.BinaryToOneHot.ports width).inputs.Values) :=
  ((Modules.BinaryToOneHot.cycleContract width).evaluate
    inputs SignalMap.emptyValues).1 .result

#guard result 0 inputs0 0
#guard !result 1 inputs1 0
#guard result 1 inputs1 1
#guard !result 2 inputs2 0
#guard result 2 inputs2 1
#guard !result 2 inputs2 2
#guard !result 2 inputs2 3
#guard !result 3 inputs3 2
#guard result 3 inputs3 3
#guard !result 3 inputs3 6

#guard BitVector.toNat 2 (inputs2 .value) == 1
#guard BitVector.toNat 3 (inputs3 .value) == 3

example (inputs : (Modules.BinaryToOneHot.ports width).inputs.Values)
    (outputs : (Modules.BinaryToOneHot.ports width).outputs.Values)
    (holds : (Modules.BinaryToOneHot.outputRule width).Holds
      inputs SignalMap.emptyValues outputs) (index : Fin (Modules.BinaryToOneHot.size width)) :
    outputs .result index = true ↔
      index.val = BitVector.toNat width (inputs .value) :=
  Modules.BinaryToOneHot.result_eq_true_iff_of_holds width inputs
    SignalMap.emptyValues outputs holds index

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (width : Nat) (fragments : List String) : Bool :=
  match renderCircuit (Modules.BinaryToOneHot.Naming.naming width) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders 0 ["binary_to_one_hot_base", "output result : UInt<1>[1]"]
#guard renders 1 ["binary_to_one_hot_recursive_1", "output result : UInt<1>[2]",
  "vector_concat_structural_bit_1_1"]
#guard renders 2 ["binary_to_one_hot_recursive_2", "output result : UInt<1>[4]",
  "lower_mask", "upper_mask"]
#guard renders 3 ["binary_to_one_hot_recursive_3", "output result : UInt<1>[8]",
  "decode_lower", "concat", "connect lower_bits.component_0, split.component_0",
  "connect invert_high.in, split.component_2"]

end Silean.Examples.Checks.BinaryToOneHot
