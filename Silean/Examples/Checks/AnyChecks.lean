import Silean.FIRRTL
import Silean.Modules.Any.Any

namespace Silean.Examples.Checks.Any

open Silean Silean.FIRRTL

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Any.ports 0) :=
  Modules.Any.certified 0

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Any.ports 5) :=
  Modules.Any.certified 5

def allFalse3 : (Modules.Any.ports 3).inputs.Values := fun | .leaf _ => false

def oneTrue3 : (Modules.Any.ports 3).inputs.Values := fun
  | .leaf index => index.val == 1

#guard !((Modules.Any.cycleContract 0).evaluate
  (fun impossible => nomatch impossible) SignalMap.emptyValues).1 .output

#guard !((Modules.Any.cycleContract 3).evaluate
  allFalse3 SignalMap.emptyValues).1 .output

#guard ((Modules.Any.cycleContract 3).evaluate
  oneTrue3 SignalMap.emptyValues).1 .output

example : Modules.Any.some 0 (fun impossible => nomatch impossible) = false := rfl

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String)
    (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit (Modules.Any.Naming.naming 0))
  ["public module any_bit_0", "inst identity of constant_false",
   "connect result, identity.out"]

#guard containsAll (renderCircuit (Modules.Any.Naming.naming 1))
  ["public module any_bit_1", "input input_0 : UInt<1>",
   "connect result, input_0"]

#guard containsAll (renderCircuit (Modules.Any.Naming.naming 5))
  ["public module any_bit_5", "input input_4 : UInt<1>",
   "inst left of any_node_bit_2_1_1",
   "inst right of any_node_bit_2_1_2_1_1", "inst combine of or_bit",
   "connect combine.left, left.result", "connect combine.right, right.result"]

end Silean.Examples.Checks.Any
