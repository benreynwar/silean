import Silean.Modules.Fifo.FifoProperties

namespace SileanTests.FifoProperties

open Silean
open Silean.Modules.Fifo
open Silean.Modules.Fifo.Properties

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
example : Silean.Modules.Fifo.PointerControl.full
    ((state1 0 2 true false) .readPointer)
    ((state1 0 2 true false) .writePointer) = true :=
  (contents_length_eq_capacity_iff_full 1 (state1 0 2 true false) (by
    unfold Invariant occupancy CircularBuffer.distance
    decide)).mp rfl

end SileanTests.FifoProperties
