import Silean2.FIRRTL
import Silean2.Modules.All

namespace Silean2.Examples.Checks.All

open Silean2 Silean2.FIRRTL

noncomputable example : ModuleCycleCertified (Modules.All.ports 0) :=
  Modules.All.certified 0

noncomputable example : ModuleCycleCertified (Modules.All.ports 5) :=
  Modules.All.certified 5

example : (Modules.Reduction.Tree.balanced 11).leafCount = 11 := by simp

example : (Modules.Reduction.Tree.balanced 11).IsBalanced := by simp

def allTrue3 : (Modules.All.ports 3).inputs.Values := fun | .leaf _ => true

def oneFalse3 : (Modules.All.ports 3).inputs.Values := fun
  | .leaf index => index.val != 1

#guard ((Modules.All.cycleContract 0).evaluate
  (fun impossible => nomatch impossible) SignalMap.emptyValues).1 .output

#guard ((Modules.All.cycleContract 3).evaluate
  allTrue3 SignalMap.emptyValues).1 .output

#guard !((Modules.All.cycleContract 3).evaluate
  oneFalse3 SignalMap.emptyValues).1 .output

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String)
    (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit (Modules.All.Naming.naming 0))
  ["public module all_bit_0", "inst identity of constant_true",
   "connect result, identity.out"]

#guard containsAll (renderCircuit (Modules.All.Naming.naming 1))
  ["public module all_bit_1", "input input_0 : UInt<1>",
   "connect result, input_0"]

#guard containsAll (renderCircuit (Modules.All.Naming.naming 5))
  ["public module all_bit_5", "input input_4 : UInt<1>",
   "inst left of all_node_bit_2_1_1",
   "inst right of all_node_bit_2_1_2_1_1", "inst combine of and_bit",
   "connect combine.left, left.result", "connect combine.right, right.result"]

end Silean2.Examples.Checks.All
