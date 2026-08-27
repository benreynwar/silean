import Silean2.Modules.FifoProperties

namespace Silean2.Examples.Checks.FifoProperties

open Silean2
open Silean2.Modules.Fifo
open Silean2.Modules.Fifo.Properties

def pointer1 (value : Fin 4) : Pointer 1
  | 0 => value.val % 2 = 1
  | 1 => value.val / 2 % 2 = 1

def state1 (read write : Fin 4) (entry0 entry1 : Bool) :
    ContractState .bit 1
  | .readPointer => pointer1 read
  | .writePointer => pointer1 write
  | .entries => fun | 0 => entry0 | 1 => entry1

def pointer0 (wrap : Bool) : Pointer 0 := fun | 0 => wrap

def state0 (readWrap writeWrap entry : Bool) : ContractState .bit 0
  | .readPointer => pointer0 readWrap
  | .writePointer => pointer0 writeWrap
  | .entries => fun | 0 => entry

def input (valid data ready reset : Bool) : Execution.Input .bit where
  enqValid := valid
  enqData := data
  deqReady := ready
  reset := reset

-- Address width zero is a genuine one-entry FIFO.
#guard capacity 0 == 1
example : contents 0 (state0 false false false) = [] := rfl
example : contents 0 (state0 false true true) = [true] := rfl

-- Logical contents follows the read pointer through physical wraparound.
example : contents 1 (state1 3 1 false true) = [true, false] := rfl

-- Empty and full boundaries agree with logical occupancy.
example : Invariant 1 (state1 0 0 false false) := by
  unfold Invariant occupancy CircularBuffer.distance
  decide
example : contents 1 (state1 0 0 false false) = [] := rfl
example : (contents 1 (state1 0 2 true false)).length = capacity 1 := rfl
example : Silean2.Modules.FifoPointerControl.full
    ((state1 0 2 true false) .readPointer)
    ((state1 0 2 true false) .writePointer) = true :=
  (contents_length_eq_capacity_iff_full 1 (state1 0 2 true false) (by
    unfold Invariant occupancy CircularBuffer.distance
    decide)).mp rfl

-- A stall and a simultaneous transfer are both covered by the cycle theorem.
example : Contracts.ResetFifo.Step (contents 1 (state1 0 1 true false))
    (Execution.step .bit 1 (state1 0 1 true false)
      (input false false false false)).observation
    (contents 1 (Execution.step .bit 1 (state1 0 1 true false)
      (input false false false false)).nextState) :=
  Execution.step_correct .bit 1 _ _ (by
    unfold Invariant occupancy CircularBuffer.distance
    decide)

example : Contracts.ResetFifo.Step (contents 1 (state1 0 1 true false))
    (Execution.step .bit 1 (state1 0 1 true false)
      (input true false true false)).observation
    (contents 1 (Execution.step .bit 1 (state1 0 1 true false)
      (input true false true false)).nextState) :=
  Execution.step_correct .bit 1 _ _ (by
    unfold Invariant occupancy CircularBuffer.distance
    decide)

-- Reset followed by traffic is handled by the same arbitrary-trace model.
example : let inputs := [input true true false true, input true false false false,
      input false false true false]
    let result := (Execution.model .bit 1).run (state1 1 2 false true) inputs
    Invariant 1 result.finalState ∧
      Contracts.ResetFifo.Transitions (contents 1 (state1 1 2 false true))
        result.observations (contents 1 result.finalState) := by
  exact Execution.run_correct .bit 1 _ _ (by
    unfold Invariant occupancy CircularBuffer.distance
    decide)

end Silean2.Examples.Checks.FifoProperties
