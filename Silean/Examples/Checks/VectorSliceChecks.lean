import Silean.FIRRTL
import Silean.Modules.VectorSlice.VectorSliceTheorems

namespace Silean.Examples.Checks.VectorSlice

open Silean Silean.FIRRTL

def pairBits : SignalType := .tuple (.cons .bit (.cons .bit .nil))

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorSlice.ports .bit 2 3 1) :=
  Modules.VectorSlice.certified .bit 2 3 1

example : (Modules.VectorSlice.moduleStructure .bit 2 3 1).HasNoBlackboxes := by
  simp only [Modules.VectorSlice.moduleStructure, ModuleStructure.HasNoBlackboxes]
  intro child
  cases child <;>
    simp [ModuleStructure.HasNoBlackboxes]

def inputs : (Modules.VectorSlice.ports .bit 2 3 1).inputs.Values
  | .value => fun | 0 => false | 1 => false | 2 => true
                  | 3 => false | 4 => true | 5 => false

def result := ((Modules.VectorSlice.cycleContract .bit 2 3 1).evaluate
  inputs SignalMap.emptyValues).1 .result

#guard result 0
#guard !result 1
#guard result 2

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorSlice.ports pairBits 0 0 2) :=
  Modules.VectorSlice.certified pairBits 0 0 2

example (inputs : (Modules.VectorSlice.ports element prefixWidth width suffixWidth).inputs.Values)
    (outputs : (Modules.VectorSlice.ports element prefixWidth width suffixWidth).outputs.Values)
    (holds : (Modules.VectorSlice.outputRule element prefixWidth width suffixWidth).Holds
      inputs SignalMap.emptyValues outputs) (index : Fin width) :
    outputs .result index =
      inputs .value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) :=
  Modules.VectorSlice.result_at_of_holds element prefixWidth width suffixWidth inputs
    SignalMap.emptyValues outputs holds index

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderCircuit (Modules.VectorSlice.naming .bit 2 3 1) with
  | .error _ => false
  | .ok text => ["public module VectorSlice_bit_2_3_1",
      "input value : UInt<1>[6]", "output result : UInt<1>[3]",
      "inst split", "inst combine",
      "connect combine.component_0, split.component_2"].all (contains text)

end Silean.Examples.Checks.VectorSlice
