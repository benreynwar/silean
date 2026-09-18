import Silean.FIRRTL
import Silean.Modules.Equality.EqualityTheorems

namespace SileanTests.Equality

open Silean Silean.FIRRTL

def emptyTuple : SignalType := .tuple .nil
def bitVector3 : SignalType := .vector 3 .bit
def nestedTuple : SignalType :=
  .tuple (.cons (.vector 2 .bit) (.cons (.tuple (.cons .bit .nil)) .nil))

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Equality.ports .bit) :=
  Modules.Equality.certified .bit

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Equality.ports emptyTuple) :=
  Modules.Equality.certified emptyTuple

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Equality.ports bitVector3) :=
  Modules.Equality.certified bitVector3

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Equality.ports nestedTuple) :=
  Modules.Equality.certified nestedTuple

def vectorEqualInputs : (Modules.Equality.ports bitVector3).inputs.Values
  | .left => fun | 0 => true | 1 => false | 2 => true
  | .right => fun | 0 => true | 1 => false | 2 => true

def vectorDifferentInputs : (Modules.Equality.ports bitVector3).inputs.Values
  | .left => fun | 0 => true | 1 => false | 2 => true
  | .right => fun | 0 => true | 1 => true | 2 => true

def nestedLeft : nestedTuple.Denote :=
  (fun | 0 => true | 1 => false, ((true, ()), ()))

def nestedRight : nestedTuple.Denote :=
  (fun | 0 => true | 1 => false, ((true, ()), ()))

def nestedDifferent : nestedTuple.Denote :=
  (fun | 0 => true | 1 => false, ((false, ()), ()))

def nestedEqualInputs : (Modules.Equality.ports nestedTuple).inputs.Values
  | .left => nestedLeft
  | .right => nestedRight

def nestedDifferentInputs : (Modules.Equality.ports nestedTuple).inputs.Values
  | .left => nestedLeft
  | .right => nestedDifferent

#guard ((Modules.Equality.cycleContract bitVector3).evaluate
  vectorEqualInputs SignalMap.emptyValues).1 .result

#guard !((Modules.Equality.cycleContract bitVector3).evaluate
  vectorDifferentInputs SignalMap.emptyValues).1 .result

#guard ((Modules.Equality.cycleContract nestedTuple).evaluate
  nestedEqualInputs SignalMap.emptyValues).1 .result

#guard !((Modules.Equality.cycleContract nestedTuple).evaluate
  nestedDifferentInputs SignalMap.emptyValues).1 .result

#guard ((Modules.Equality.cycleContract emptyTuple).evaluate
  (fun | .left | .right => ()) SignalMap.emptyValues).1 .result

example (signalType : SignalType)
    (inputs : (Modules.Equality.ports signalType).inputs.Values)
    (outputs : (Modules.Equality.ports signalType).outputs.Values)
    (holds : (Modules.Equality.outputRule signalType).Holds
      inputs SignalMap.emptyValues outputs) :
    outputs .result = true ↔ inputs .left = inputs .right :=
  Modules.Equality.output_eq_true_iff_of_holds signalType inputs
    SignalMap.emptyValues outputs holds

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String)
    (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit (Modules.Equality.Naming.naming .bit))
  ["public module equality_bit", "inst gate of eq_bit",
   "connect result, gate.out"]

#guard containsAll (renderCircuit (Modules.Equality.Naming.naming emptyTuple))
  ["public module equality_structural", "inst split_left",
   "inst split_right", "inst all of all_bit_0"]

#guard containsAll (renderCircuit (Modules.Equality.Naming.naming bitVector3))
  ["public module equality_structural", "inst split_left",
   "inst equal_component_0", "inst equal_component_2", "inst all"]

#guard containsAll (renderCircuit (Modules.Equality.Naming.naming nestedTuple))
  ["public module equality_structural", "inst equal_component_0",
   "inst equal_component_1", "inst all"]

end SileanTests.Equality
