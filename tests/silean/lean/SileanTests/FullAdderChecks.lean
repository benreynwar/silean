import Silean.FIRRTL
import Silean.Modules.FullAdder.FullAdderDerived

namespace SileanTests.FullAdder

open Silean Silean.FIRRTL

example : Modules.FullAdder.description.inputs.map (·.name) =
    [("left" : Naming.SourceName), "right", "carryIn"] := rfl

example : Modules.FullAdder.description.children.map (·.name) =
    [.indexed "half_adder" 0, .indexed "half_adder" 1, .indexed "or" 0] := rfl

example : Authoring.CircuitDescription.Description.ImplementsCycleContract
    Modules.FullAdder.description Modules.FullAdder.cycleContract
      Modules.FullAdder.Naming.ports :=
  Modules.FullAdder.construction_correct

noncomputable example : Contracts.Cycle.ModuleCycleCertified Modules.FullAdder.ports :=
  Modules.FullAdder.certified

noncomputable example := Modules.FullAdder.certifiedLayer.certify

def inputs (left right carryIn : Bool) : Modules.FullAdder.ports.inputs.Values
  | .left => left
  | .right => right
  | .carryIn => carryIn

def result (left right carryIn : Bool) :=
  (Modules.FullAdder.cycleContract.evaluate
    (inputs left right carryIn) SignalMap.emptyValues).1

#guard !(result false false false .sum) && !(result false false false .carryOut)
#guard result false false true .sum && !(result false false true .carryOut)
#guard result false true false .sum && !(result false true false .carryOut)
#guard !(result false true true .sum) && result false true true .carryOut
#guard result true false false .sum && !(result true false false .carryOut)
#guard !(result true false true .sum) && result true false true .carryOut
#guard !(result true true false .sum) && result true true false .carryOut
#guard result true true true .sum && result true true true .carryOut

example (left right carryIn : Bool) :
    (result left right carryIn .sum).toNat +
        2 * (result left right carryIn .carryOut).toNat =
      left.toNat + right.toNat + carryIn.toNat := by
  exact Modules.FullAdder.numeric_value_of_allowed
    (Modules.FullAdder.cycleContract.evaluateStep_allowed
      (inputs left right carryIn) SignalMap.emptyValues)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule Modules.FullAdder.design.naming with
  | .error _ => false
  | .ok text =>
      ["public module FullAdder",
       "input left : UInt<1>", "input right : UInt<1>",
       "input carryIn : UInt<1>",
       "output sum : UInt<1>", "output carryOut : UInt<1>",
       "inst half_adder_0 of HalfAdder",
       "inst half_adder_1 of HalfAdder",
       "inst or_0 of or_bit",
       "connect half_adder_1.left, half_adder_0.sum",
       "connect or_0.left, half_adder_0.carry",
       "connect or_0.right, half_adder_1.carry"].all (contains text)

end SileanTests.FullAdder
