import Silean.FIRRTL
import Silean.Modules.Fifo.FifoPointerControlCertified

namespace Silean.Examples.Checks.FifoPointerControl

open Silean Silean.Modules.Fifo.PointerControl
open Silean.FIRRTL

-- Pointer bits are LSB-first: address bits precede the final wrap bit.
def addressOneWrapZero : Pointer 2 := fun
  | 0 => true
  | 1 => false
  | 2 => false

def addressTwoWrapZero : Pointer 2 := fun
  | 0 => false
  | 1 => true
  | 2 => false

def addressOneWrapOne : Pointer 2 := fun
  | 0 => true
  | 1 => false
  | 2 => true

#guard pointerAddress addressOneWrapZero 0
#guard !(pointerAddress addressOneWrapZero 1)
#guard !(pointerWrap addressOneWrapZero)
#guard pointerWrap addressOneWrapOne

-- Unequal addresses are neither empty nor full.
#guard !(empty addressOneWrapZero addressTwoWrapZero)
#guard !(full addressOneWrapZero addressTwoWrapZero)
#guard inputReady addressOneWrapZero addressTwoWrapZero
#guard outputValid addressOneWrapZero addressTwoWrapZero

-- Equal complete pointers denote an empty FIFO.
#guard empty addressOneWrapZero addressOneWrapZero
#guard !(full addressOneWrapZero addressOneWrapZero)
#guard inputReady addressOneWrapZero addressOneWrapZero
#guard !(outputValid addressOneWrapZero addressOneWrapZero)
#guard !(readAdvance addressOneWrapZero addressOneWrapZero true)

-- Matching addresses with different wrap bits denote a full FIFO.
#guard !(empty addressOneWrapZero addressOneWrapOne)
#guard full addressOneWrapZero addressOneWrapOne
#guard !(inputReady addressOneWrapZero addressOneWrapOne)
#guard outputValid addressOneWrapZero addressOneWrapOne
#guard !(writeAdvance addressOneWrapZero addressOneWrapOne true)

-- Both transfers may advance in the same nonempty, nonfull cycle.
#guard readAdvance addressOneWrapZero addressTwoWrapZero true
#guard writeAdvance addressOneWrapZero addressTwoWrapZero true

def inputs : (ports 2).inputs.Values
  | .readPointer => addressOneWrapZero
  | .writePointer => addressTwoWrapZero
  | .inputValid => true
  | .outputReady => true

def outputs := ((cycleContract 2).evaluate inputs SignalMap.emptyValues).1

-- Parent-facing observations do not inherit the unrelated handshake inputs.
example : (readAddressRule 2).readsInputs.labels = [.readPointer] := rfl
example : (outputValidRule 2).readsInputs.labels =
    [.readPointer, .writePointer] := rfl
example : (inputReadyRule 2).readsInputs.labels =
    [.readPointer, .writePointer] := rfl

#guard outputs .readAddress 0
#guard !(outputs .readAddress 1)
#guard !(outputs .writeAddress 0)
#guard outputs .writeAddress 1
#guard outputs .inputReady
#guard outputs .outputValid
#guard outputs .readAdvance
#guard outputs .writeAdvance

example : (readAddressRule 2).Holds inputs SignalMap.emptyValues outputs := by
  exact ((cycleContract 2).evaluate_evaluatesTo inputs SignalMap.emptyValues).1
    .readAddress

example : (inputReadyRule 2).Holds inputs SignalMap.emptyValues outputs := by
  exact ((cycleContract 2).evaluate_evaluatesTo inputs SignalMap.emptyValues).1
    .inputReady

-- At address width zero, the sole pointer bit is the wrap bit and the address
-- value is the unique empty vector.
def wrapZero : Pointer 0 := fun | 0 => false
def wrapOne : Pointer 0 := fun | 0 => true

#guard empty wrapZero wrapZero
#guard !(full wrapZero wrapZero)
#guard !(empty wrapZero wrapOne)
#guard addressesEqual wrapZero wrapOne
#guard wrapsDiffer wrapZero wrapOne
#guard full wrapZero wrapOne

example : pointerAddress wrapZero = pointerAddress wrapOne := by
  funext index
  exact Fin.elim0 index

example (readPointer writePointer : Pointer 2)
    (isEmpty : empty readPointer writePointer = true) :
    full readPointer writePointer = false :=
  empty_implies_not_full readPointer writePointer isEmpty

example (readPointer writePointer : Pointer 2)
    (isFull : full readPointer writePointer = true) :
    empty readPointer writePointer = false :=
  full_implies_not_empty readPointer writePointer isFull

noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports 0) := certified 0
noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports 2) := certified 2

noncomputable def structuralState (addressWidth : Nat) :
    (moduleStructure addressWidth).State :=
  (moduleStructure addressWidth).structuralState.defaultValues

example : ∃ proposal,
    (moduleStructure 2).IsSolution inputs (structuralState 2) proposal ∧
    ∀ other, (moduleStructure 2).IsSolution inputs (structuralState 2) other →
      other = proposal :=
  (certified 2).hasExactlyOneStructuralResult inputs (structuralState 2)

def zeroInputs : (ports 0).inputs.Values
  | .readPointer => wrapZero
  | .writePointer => wrapOne
  | .inputValid => true
  | .outputReady => true

example : ∃ proposal,
    (moduleStructure 0).IsSolution zeroInputs (structuralState 0) proposal ∧
    ∀ other, (moduleStructure 0).IsSolution zeroInputs (structuralState 0) other →
      other = proposal :=
  (certified 0).hasExactlyOneStructuralResult zeroInputs (structuralState 0)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (addressWidth : Nat) (fragments : List String) : Bool :=
  match renderCircuit (naming addressWidth) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders 2
  ["public module PointerControl_2",
   "inst readSplit of split_aggregate_v3_bit",
   "inst readAddressCombiner of combine_aggregate_v2_bit",
   "inst addressEquality of equality_structural_v2_bit",
   "inst wrapEquality of eq_bit",
   "inst emptyGate of and_bit",
   "inst fullGate of and_bit"]

#guard renders 0
  ["public module PointerControl_0",
   "input readPointer : UInt<1>[1]",
   "output readAddress : UInt<1>[0]",
   "inst addressEquality of equality_structural_v0_bit"]

end Silean.Examples.Checks.FifoPointerControl
