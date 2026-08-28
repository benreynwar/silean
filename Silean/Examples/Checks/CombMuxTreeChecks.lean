import Silean.FIRRTL
import Silean.Modules.CombMuxTree
import Silean.Composition.SignalLogic

namespace Silean.Examples.Checks.CombMuxTree

open Silean Silean.FIRRTL

def pairBits : SignalType := .tuple (.cons .bit (.cons .bit .nil))

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.CombMuxTree.ports .bit 0) :=
  Modules.CombMuxTree.certified .bit 0
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.CombMuxTree.ports .bit 1) :=
  Modules.CombMuxTree.certified .bit 1
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.CombMuxTree.ports .bit 2) :=
  Modules.CombMuxTree.certified .bit 2
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.CombMuxTree.ports .bit 3) :=
  Modules.CombMuxTree.certified .bit 3
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.CombMuxTree.ports pairBits 2) :=
  Modules.CombMuxTree.certified pairBits 2

def inputs0 : (Modules.CombMuxTree.ports .bit 0).inputs.Values
  | .values => fun | 0 => true
  | .index => fun impossible => Fin.elim0 impossible

def inputs1 : (Modules.CombMuxTree.ports .bit 1).inputs.Values
  | .values => fun | 0 => false | 1 => true
  | .index => fun | 0 => true

def inputs2 : (Modules.CombMuxTree.ports .bit 2).inputs.Values
  | .values => fun | 0 => false | 1 => true | 2 => false | 3 => true
  | .index => fun | 0 => true | 1 => false

def inputs3 : (Modules.CombMuxTree.ports .bit 3).inputs.Values
  | .values => fun
      | 0 => false | 1 => false | 2 => false | 3 => true
      | 4 => false | 5 => false | 6 => false | 7 => false
  | .index => fun | 0 => true | 1 => true | 2 => false

def bitResult (width : Nat)
    (inputs : (Modules.CombMuxTree.ports .bit width).inputs.Values) :=
  ((Modules.CombMuxTree.cycleContract .bit width).evaluate
    inputs SignalMap.emptyValues).1 .result

#guard bitResult 0 inputs0
#guard bitResult 1 inputs1
#guard bitResult 2 inputs2
#guard bitResult 3 inputs3

def aggregateInputs : (Modules.CombMuxTree.ports pairBits 2).inputs.Values
  | .values => fun
      | 0 => (false, (false, ()))
      | 1 => (false, (true, ()))
      | 2 => (true, (false, ()))
      | 3 => (true, (true, ()))
  | .index => fun | 0 => true | 1 => false

def aggregateResult := ((Modules.CombMuxTree.cycleContract pairBits 2).evaluate
  aggregateInputs SignalMap.emptyValues).1 .result

#guard pairBits.equal aggregateResult (false, (true, ()))

example (inputs : (Modules.CombMuxTree.ports element width).inputs.Values)
    (outputs : (Modules.CombMuxTree.ports element width).outputs.Values)
    (holds : (Modules.CombMuxTree.outputRule element width).Holds
      inputs SignalMap.emptyValues outputs) :
    outputs .result = inputs .values
      ⟨BitVector.toNat width (inputs .index),
        BitVector.toNat_lt_cardinality width (inputs .index)⟩ :=
  Modules.CombMuxTree.result_of_holds element width inputs SignalMap.emptyValues
    outputs holds

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (element : SignalType) (width : Nat)
    (fragments : List String) : Bool :=
  match renderCircuit (Modules.CombMuxTree.Naming.naming element width) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders .bit 0 ["public module comb_mux_tree_base_bit",
  "input values : UInt<1>[1]", "output result : UInt<1>"]
#guard renders .bit 1 ["public module comb_mux_tree_recursive_bit_1",
  "inst split_values", "inst select_lower", "inst select_upper", "inst mux"]
#guard renders .bit 2 ["public module comb_mux_tree_recursive_bit_2",
  "vector_split_structural_bit_2_2", "comb_mux_tree_recursive_bit_1"]
#guard renders .bit 3 ["public module comb_mux_tree_recursive_bit_3",
  "input values : UInt<1>[8]", "input index : UInt<1>[3]",
  "connect combine_index_lower.component_0, split_index.component_0",
  "connect mux.select, split_index.component_2"]
#guard renders pairBits 2 ["public module comb_mux_tree_recursive",
  "output result : {", "inst mux"]

end Silean.Examples.Checks.CombMuxTree
