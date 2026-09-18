import Silean.FIRRTL
import Silean.Foundation.BitVector
import Silean.Modules.BitwiseOr.BitwiseOr

namespace SileanTests.BitwiseOr

open Silean Silean.FIRRTL

abbrev vectorType : SignalType := .vector 3 .bit
abbrev nestedType : SignalType :=
  .tuple (.ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))])

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.BitwiseOr.ports vectorType) := Modules.BitwiseOr.certified vectorType
noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.BitwiseOr.ports nestedType) := Modules.BitwiseOr.certified nestedType

def vectorLeft : vectorType.Denote := fun | 0 | 1 => true | 2 => false
def vectorRight : vectorType.Denote := fun | 0 | 2 => true | 1 => false

def nestedLeft : nestedType.Denote :=
  (false, (fun index => bif index = 0 then (false, (true, ()))
    else (true, (false, ())), ()))

def nestedRight : nestedType.Denote :=
  (true, (fun index => bif index = 0 then (true, (true, ()))
    else (false, (true, ())), ()))

def inputs (signalType : SignalType) (left right : signalType.Denote) :
    (Modules.BitwiseOr.ports signalType).inputs.Values
  | .left => left
  | .right => right

def result (signalType : SignalType) (left right : signalType.Denote) :=
  ((Modules.BitwiseOr.cycleContract signalType).evaluate
    (inputs signalType left right) SignalMap.emptyValues).1 .result

#guard !(show Bool from result .bit false false)
#guard show Bool from result .bit false true
#guard show Bool from result .bit true false
#guard show Bool from result .bit true true
#guard BitVector.toNat 3 (result vectorType vectorLeft vectorRight) == 7
#guard nestedType.equal (result nestedType nestedLeft nestedRight)
  (nestedType.bitwiseOr nestedLeft nestedRight)

example (signalType : SignalType) (left right : signalType.Denote) :
    result signalType left right = signalType.bitwiseOr left right := by
  have allowed := (Modules.BitwiseOr.cycleContract signalType).evaluateStep_allowed
    (inputs signalType left right) SignalMap.emptyValues
  simpa [result, inputs, Contracts.Cycle.ModuleCycleContract.evaluateStep] using
    Modules.BitwiseOr.result_of_allowed signalType allowed

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.BitwiseOr.Naming.naming vectorType) with
  | .error _ => false
  | .ok text =>
      ["public module bitwise_or_structural", "input left : UInt<1>[3]",
       "input right : UInt<1>[3]", "output result : UInt<1>[3]",
       "inst split_left", "inst split_right", "inst or_component_0",
       "inst combine"].all (contains text)

end SileanTests.BitwiseOr
