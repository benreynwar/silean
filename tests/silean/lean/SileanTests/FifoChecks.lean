import Silean.FIRRTL
import Silean.Modules.Fifo.FifoCycleTheorems
import Silean.Emitters.StructuredPayload

namespace SileanTests.Fifo

open Silean Silean.FIRRTL Silean.Interfaces.Fifo Silean.Modules.Fifo

def pointer1 (value : Fin 4) : Pointer 1
  | 0 => value.val % 2 = 1
  | 1 => value.val / 2 % 2 = 1

def inputs (valid data ready reset : Bool) : (ports .bit).inputs.Values
  | .inputValid => valid
  | .inputData => data
  | .outputReady => ready
  | .reset => reset

-- The registered FIFO exposes its two interface directions independently.
-- Neither current-cycle output depends on a current-cycle handshake input.
example : (forwardRule .bit 1).readsInputs.labels = [] := rfl
example : (readyRule .bit 1).readsInputs.labels = [] := rfl
example : (forwardRule .bit 1).writesOutputs.labels =
    [.outputValid, .outputData] := rfl
example : (readyRule .bit 1).writesOutputs.labels = [.inputReady] := rfl

def state1 (read write : Fin 4) (entry0 entry1 : Bool) :
    (stateMap .bit 1).Values
  | .readPointer => pointer1 read
  | .writePointer => pointer1 write
  | .entries => fun | 0 => entry0 | 1 => entry1

def cycle1 (valid data ready reset : Bool)
    (state : (stateMap .bit 1).Values) :=
  (cycleContract .bit 1).evaluate (inputs valid data ready reset) state

def emptyState := state1 0 0 false false
def enqueued := (cycle1 true true false false emptyState).2

-- Empty is ready but not valid; an enqueue writes entry zero and advances only write.
#guard !(cycle1 false false false false emptyState).1 .outputValid
#guard (cycle1 false false false false emptyState).1 .inputReady
#guard BitVector.toNat 2 (enqueued .readPointer) == 0
#guard BitVector.toNat 2 (enqueued .writePointer) == 1
#guard enqueued .entries 0

-- The next cycle exposes the oldest stored value, and an accepted dequeue empties it.
#guard (cycle1 false false false false enqueued).1 .outputValid
#guard (cycle1 false false false false enqueued).1 .outputData
def dequeued := (cycle1 false false true false enqueued).2
#guard BitVector.toNat 2 (dequeued .readPointer) == 1
#guard BitVector.toNat 2 (dequeued .writePointer) == 1
#guard !(cycle1 false false false false dequeued).1 .outputValid

-- A full two-entry FIFO blocks input and retains both pointers when stalled.
def fullState := state1 0 2 true false
#guard (cycle1 true true false false fullState).1 .outputValid
#guard !(cycle1 true true false false fullState).1 .inputReady
#guard BitVector.toNat 2 ((cycle1 true true false false fullState).2 .writePointer) == 2

-- Away from the boundaries, input and output transfers can occur together.
def middleState := state1 0 1 true false
def simultaneous := cycle1 true true true false middleState
#guard simultaneous.1 .outputValid
#guard simultaneous.1 .inputReady
#guard simultaneous.1 .outputData
#guard BitVector.toNat 2 (simultaneous.2 .readPointer) == 1
#guard BitVector.toNat 2 (simultaneous.2 .writePointer) == 2
#guard simultaneous.2 .entries 1

-- Two accepted inputs emerge in the same order on successive accepted outputs.
def orderedFirst := (cycle1 true true false false emptyState).2
def orderedSecond := (cycle1 true false false false orderedFirst).2
#guard (cycle1 false false true false orderedSecond).1 .outputData
def afterFirstOutput := (cycle1 false false true false orderedSecond).2
#guard !(cycle1 false false true false afterFirstOutput).1 .outputData

-- With neither transfer accepted, pointers and storage are retained.
def retained := (cycle1 false true false false middleState).2
#guard BitVector.toNat 2 (retained .readPointer) == 0
#guard BitVector.toNat 2 (retained .writePointer) == 1
#guard retained .entries 0
#guard !(retained .entries 1)

-- Pointer arithmetic carries into the wrap bit and then rolls over.
#guard BitVector.toNat 2 ((cycle1 true true false false (state1 0 1 false false)).2
  .writePointer) == 2
#guard BitVector.toNat 2 ((cycle1 true true false false (state1 2 3 false false)).2
  .writePointer) == 0

-- Reset wins over both pointer advances and makes the following state empty.
def resetState := (cycle1 true true true true (state1 1 2 false true)).2
#guard BitVector.toNat 2 (resetState .readPointer) == 0
#guard BitVector.toNat 2 (resetState .writePointer) == 0
-- Reset does not clear or suppress the bank's ordinary accepted write.
#guard resetState .entries 0
#guard !(cycle1 false false false false resetState).1 .outputValid
#guard (cycle1 false false false false resetState).1 .inputReady

example :
    let nextState := (stateRule .bit 1).apply
      (inputs true true true true) (state1 1 2 false true)
    outputValid (nextState .readPointer) (nextState .writePointer) = false ∧
      inputReady (nextState .readPointer) (nextState .writePointer) = true :=
  empty_after_reset .bit 1 _ _ rfl

-- Address width zero is a real one-entry FIFO; the sole pointer bit is wrap.
def pointer0 (wrap : Bool) : Pointer 0 := fun | 0 => wrap
def state0 (readWrap writeWrap entry : Bool) : (stateMap .bit 0).Values
  | .readPointer => pointer0 readWrap
  | .writePointer => pointer0 writeWrap
  | .entries => fun | 0 => entry
def cycle0 (valid data ready reset : Bool) (state : (stateMap .bit 0).Values) :=
  (cycleContract .bit 0).evaluate (inputs valid data ready reset) state
def oneEnqueued := (cycle0 true true false false (state0 false false false)).2
#guard oneEnqueued .writePointer 0
#guard oneEnqueued .entries 0
#guard (cycle0 false false false false oneEnqueued).1 .outputValid
#guard !(cycle0 false false false false oneEnqueued).1 .inputReady

noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports .bit) :=
  certified .bit 0
noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports (.vector 3 .bit)) :=
  certified (.vector 3 .bit) 2

def middleStep := (cycleContract .bit 1).evaluateStep
  (inputs true true true false) middleState

-- The public Step interface exposes the same boundary behavior and state
-- transition without mentioning the FIFO's child hierarchy.
example : middleStep.outputs .inputReady =
    inputReady (middleStep.currentState .readPointer)
      (middleStep.currentState .writePointer) :=
  input_ready_of_allowed
    ((cycleContract .bit 1).evaluateStep_allowed _ _)

example : middleStep.nextState .entries =
    nextEntries 1 (middleStep.inputs .inputValid) (middleStep.inputs .inputData)
      (middleStep.currentState .readPointer)
      (middleStep.currentState .writePointer)
      (middleStep.currentState .entries) :=
  next_entries_of_allowed
    ((cycleContract .bit 1).evaluateStep_allowed _ _)

example : Contracts.Cycle.Implements (moduleStructure .bit 1)
    (cycleContract .bit 1) (certification .bit 1).stateCorresponds :=
  implements_cycle_contract .bit 1

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (addressWidth : Nat) (fragments : List String) : Bool :=
  match renderCircuit (Silean.Modules.Fifo.naming .bit addressWidth) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders 2
  ["public module Fifo_bit_2",
   "input input_valid : UInt<1>", "input reset : UInt<1>",
   "output output_valid : UInt<1>", "output input_ready : UInt<1>",
   "inst readCounter of EnabledResetCounter_3_0_0_0",
   "inst writeCounter of EnabledResetCounter_3_0_0_0",
   "inst fifo_pointer_control_0 of PointerControl_2",
   "inst register_bank_0 of RegisterBank_bit_2_1",
   "connect fifo_pointer_control_0.readPointer, readCounter.value",
   "connect register_bank_0.write_enable, writeAdvance"]

#guard renders 0
  ["public module Fifo_bit_0",
   "inst fifo_pointer_control_0 of PointerControl_0",
   "inst register_bank_0 of RegisterBank_bit_0_1"]

#guard match renderCircuit
    (Silean.Modules.Fifo.Naming.namingWith
      Silean.Emitters.StructuredPayload.type 2
      Silean.Emitters.StructuredPayload.naming) with
  | .error _ => false
  | .ok text =>
      (["input input_data : { a : UInt<1>[3], b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] } }",
       "output output_data : { a : UInt<1>[3], b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] } }",
       "input write_value : { a : UInt<1>[3], b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] } }"]).all
        (contains text)

end SileanTests.Fifo
