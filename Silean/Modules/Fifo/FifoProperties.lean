import Silean.Modules.Fifo.Internal.FifoPropertiesVerification

/-! # Pointer FIFO queue properties

This is the public theorem interface for the logical queue view defined in
`Fifo.lean`. The arithmetic and circular-buffer proof implementation lives
under `Internal`.
-/

namespace Silean.Modules.Fifo.Properties

open Silean Silean.Interfaces.Fifo

@[simp] theorem contents_length (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    (contents addressWidth state).length =
      occupancy addressWidth (state .readPointer) (state .writePointer) :=
  Internal.contents_length addressWidth state

theorem contents_bounded (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (invariant : Invariant addressWidth state) :
    (contents addressWidth state).length ≤ capacity addressWidth :=
  Internal.contents_bounded addressWidth state invariant

theorem occupancy_eq_zero_iff (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) :
    occupancy addressWidth readPointer writePointer = 0 ↔
      readPointer = writePointer :=
  Internal.occupancy_eq_zero_iff addressWidth readPointer writePointer

theorem occupancy_eq_capacity_iff_full (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth)
    (valid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth) :
    occupancy addressWidth readPointer writePointer = capacity addressWidth ↔
      PointerControl.full readPointer writePointer = true :=
  Internal.occupancy_eq_capacity_iff_full addressWidth readPointer writePointer valid

theorem occupancy_eq_zero_iff_empty (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) :
    occupancy addressWidth readPointer writePointer = 0 ↔
      PointerControl.empty readPointer writePointer = true :=
  Internal.occupancy_eq_zero_iff_empty addressWidth readPointer writePointer

theorem contents_eq_nil_iff_empty (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    contents addressWidth state = [] ↔
      PointerControl.empty (state .readPointer) (state .writePointer) = true :=
  Internal.contents_eq_nil_iff_empty addressWidth state

theorem contents_length_eq_capacity_iff_full (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (valid : Invariant addressWidth state) :
    (contents addressWidth state).length = capacity addressWidth ↔
      PointerControl.full (state .readPointer) (state .writePointer) = true :=
  Internal.contents_length_eq_capacity_iff_full addressWidth state valid

theorem outputValid_eq_contents_nonempty (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    Fifo.outputValid (state .readPointer) (state .writePointer) =
      !(contents addressWidth state).isEmpty :=
  Internal.outputValid_eq_contents_nonempty addressWidth state

theorem inputReady_eq_contents_below_capacity (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (valid : Invariant addressWidth state) :
    Fifo.inputReady (state .readPointer) (state .writePointer) =
      decide ((contents addressWidth state).length < capacity addressWidth) :=
  Internal.inputReady_eq_contents_below_capacity addressWidth state valid

theorem outputData_eq_contents_head (addressWidth : Nat)
    (state : ContractState element addressWidth) (head : Word element)
    (tail : List (Word element))
    (equal : contents addressWidth state = head :: tail) :
    Fifo.outputData addressWidth (state .readPointer) (state .entries) = head :=
  Internal.outputData_eq_contents_head addressWidth state head tail equal

theorem contentsOf_next_of_notReset (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool) (data : Word element)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth) :
    contentsOf addressWidth entries readPointer writePointer ++
        (bif writeAdvance readPointer writePointer validInput then [data] else []) =
      (bif readAdvance readPointer writePointer ready then
          [outputData addressWidth readPointer entries] else []) ++
        contentsOf addressWidth
          (nextEntries addressWidth validInput data readPointer writePointer entries)
          (nextReadPointer addressWidth false ready readPointer writePointer)
          (nextWritePointer addressWidth false validInput readPointer writePointer) :=
  Internal.contentsOf_next_of_notReset addressWidth entries readPointer writePointer
    ready validInput data stateValid

theorem stalled_contents (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool) (data : Word element)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth)
    (noRead : readAdvance readPointer writePointer ready = false)
    (noWrite : writeAdvance readPointer writePointer validInput = false) :
    contentsOf addressWidth
        (nextEntries addressWidth validInput data readPointer writePointer entries)
        (nextReadPointer addressWidth false ready readPointer writePointer)
        (nextWritePointer addressWidth false validInput readPointer writePointer) =
      contentsOf addressWidth entries readPointer writePointer :=
  Internal.stalled_contents addressWidth entries readPointer writePointer ready
    validInput data stateValid noRead noWrite

theorem enqueue_appends (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool) (data : Word element)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth)
    (noRead : readAdvance readPointer writePointer ready = false)
    (writeAccepted : writeAdvance readPointer writePointer validInput = true) :
    contentsOf addressWidth
        (nextEntries addressWidth validInput data readPointer writePointer entries)
        (nextReadPointer addressWidth false ready readPointer writePointer)
        (nextWritePointer addressWidth false validInput readPointer writePointer) =
      contentsOf addressWidth entries readPointer writePointer ++ [data] :=
  Internal.enqueue_appends addressWidth entries readPointer writePointer ready
    validInput data stateValid noRead writeAccepted

theorem dequeue_removes_oldest (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool) (data : Word element)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth)
    (readAccepted : readAdvance readPointer writePointer ready = true)
    (noWrite : writeAdvance readPointer writePointer validInput = false) :
    contentsOf addressWidth entries readPointer writePointer =
      outputData addressWidth readPointer entries ::
        contentsOf addressWidth
          (nextEntries addressWidth validInput data readPointer writePointer entries)
          (nextReadPointer addressWidth false ready readPointer writePointer)
          (nextWritePointer addressWidth false validInput readPointer writePointer) :=
  Internal.dequeue_removes_oldest addressWidth entries readPointer writePointer ready
    validInput data stateValid readAccepted noWrite

theorem simultaneous_transfer_preserves_order (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool) (data : Word element)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth)
    (readAccepted : readAdvance readPointer writePointer ready = true)
    (writeAccepted : writeAdvance readPointer writePointer validInput = true) :
    contentsOf addressWidth entries readPointer writePointer ++ [data] =
      outputData addressWidth readPointer entries ::
        contentsOf addressWidth
          (nextEntries addressWidth validInput data readPointer writePointer entries)
          (nextReadPointer addressWidth false ready readPointer writePointer)
          (nextWritePointer addressWidth false validInput readPointer writePointer) :=
  Internal.simultaneous_transfer_preserves_order addressWidth entries readPointer
    writePointer ready validInput data stateValid readAccepted writeAccepted

end Silean.Modules.Fifo.Properties
