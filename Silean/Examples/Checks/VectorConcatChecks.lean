import Silean.FIRRTL
import Silean.Modules.VectorConcat.VectorConcatCertified
import Silean.Composition.SignalLogic

namespace Silean.Examples.Checks.VectorConcat

open Silean Silean.FIRRTL

def pairBits : SignalType := .tuple (.cons .bit (.cons .bit .nil))

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorConcat.ports .bit 0 3) :=
  Modules.VectorConcat.certified .bit 0 3

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorConcat.ports .bit 2 0) :=
  Modules.VectorConcat.certified .bit 2 0

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorConcat.ports .bit 2 3) :=
  Modules.VectorConcat.certified .bit 2 3

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.VectorConcat.ports pairBits 1 2) :=
  Modules.VectorConcat.certified pairBits 1 2

def bitInputs : (Modules.VectorConcat.ports .bit 2 3).inputs.Values
  | .left => fun | 0 => true | 1 => false
  | .right => fun | 0 => false | 1 => true | 2 => true

def bitResult := ((Modules.VectorConcat.cycleContract .bit 2 3).evaluate
  bitInputs SignalMap.emptyValues).1 .result

#guard bitResult 0
#guard !bitResult 1
#guard !bitResult 2
#guard bitResult 3
#guard bitResult 4

def emptyLeftInputs : (Modules.VectorConcat.ports .bit 0 2).inputs.Values
  | .left => fun index => Fin.elim0 index
  | .right => fun | 0 => true | 1 => false

#guard ((Modules.VectorConcat.cycleContract .bit 0 2).evaluate
  emptyLeftInputs SignalMap.emptyValues).1 .result 0

#guard !((Modules.VectorConcat.cycleContract .bit 0 2).evaluate
  emptyLeftInputs SignalMap.emptyValues).1 .result 1

def emptyRightInputs : (Modules.VectorConcat.ports .bit 2 0).inputs.Values
  | .left => fun | 0 => false | 1 => true
  | .right => fun index => Fin.elim0 index

#guard !((Modules.VectorConcat.cycleContract .bit 2 0).evaluate
  emptyRightInputs SignalMap.emptyValues).1 .result 0

#guard ((Modules.VectorConcat.cycleContract .bit 2 0).evaluate
  emptyRightInputs SignalMap.emptyValues).1 .result 1

def aggregateInputs : (Modules.VectorConcat.ports pairBits 1 2).inputs.Values
  | .left => fun | 0 => (true, (false, ()))
  | .right => fun
      | 0 => (false, (true, ()))
      | 1 => (true, (true, ()))

def aggregateResult := ((Modules.VectorConcat.cycleContract pairBits 1 2).evaluate
  aggregateInputs SignalMap.emptyValues).1 .result

#guard pairBits.equal (aggregateResult 0) (true, (false, ()))
#guard pairBits.equal (aggregateResult 1) (false, (true, ()))
#guard pairBits.equal (aggregateResult 2) (true, (true, ()))

example (inputs : (Modules.VectorConcat.ports element leftWidth rightWidth).inputs.Values)
    (outputs : (Modules.VectorConcat.ports element leftWidth rightWidth).outputs.Values)
    (holds : (Modules.VectorConcat.outputRule element leftWidth rightWidth).Holds
      inputs SignalMap.emptyValues outputs) (index : Fin leftWidth) :
    outputs .result (Fin.castAdd rightWidth index) = inputs .left index :=
  Modules.VectorConcat.result_left_of_holds element leftWidth rightWidth inputs
    SignalMap.emptyValues outputs holds index

example (inputs : (Modules.VectorConcat.ports element leftWidth rightWidth).inputs.Values)
    (outputs : (Modules.VectorConcat.ports element leftWidth rightWidth).outputs.Values)
    (holds : (Modules.VectorConcat.outputRule element leftWidth rightWidth).Holds
      inputs SignalMap.emptyValues outputs) (index : Fin rightWidth) :
    outputs .result (Fin.natAdd leftWidth index) = inputs .right index :=
  Modules.VectorConcat.result_right_of_holds element leftWidth rightWidth inputs
    SignalMap.emptyValues outputs holds index

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String)
    (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit (Modules.VectorConcat.naming .bit 0 3))
  ["public module VectorConcat_bit_0_3", "inst leftSplit",
   "inst rightSplit", "inst combine", "output result : UInt<1>[3]"]

#guard containsAll (renderCircuit (Modules.VectorConcat.naming .bit 2 0))
  ["public module VectorConcat_bit_2_0", "input left : UInt<1>[2]",
   "output result : UInt<1>[2]"]

#guard containsAll (renderCircuit (Modules.VectorConcat.naming .bit 2 3))
  ["public module VectorConcat_bit_2_3", "input left : UInt<1>[2]",
   "input right : UInt<1>[3]", "output result : UInt<1>[5]",
   "connect combine.component_0, leftSplit.component_0",
   "connect combine.component_4, rightSplit.component_2"]

#guard containsAll (renderCircuit (Modules.VectorConcat.naming pairBits 1 2))
  ["public module VectorConcat", "inst leftSplit",
   "inst rightSplit", "inst combine"]

end Silean.Examples.Checks.VectorConcat
