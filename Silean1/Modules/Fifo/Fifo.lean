import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.FifoPorts
import Silean.Interfaces.FifoPorts
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Fifo.CircularBuffer
import Silean.Modules.Fifo.FifoPointerControlDerived
import Silean.Modules.RegisterBank.RegisterBankDerived
import Silean.Naming.FifoPortsNaming

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo

/-! A FIFO with `2 ^ addressWidth` entries of `element`, built from a register
bank with read and write pointers.

The extra high bit in each pointer distinguishes a full buffer from an empty
one when their address bits are equal. Reset is synchronous; invalid storage
contents do not need to be cleared. -/

open Authoring.CircuitDescription
open Silean.Interfaces.Fifo.ports

abbrev Pointer (addressWidth : Nat) :=
  EnabledResetCounter.Value (addressWidth + 1)

/-- Both counters start at the first entry, making the FIFO empty. -/
def zeroPointer (addressWidth : Nat) : Pointer addressWidth := fun _ => false

/-! ## Authored hardware -/

noncomputable def construction (element : SignalType) (addressWidth : Nat) :
    ModuleBuilder (ports element) Unit := do
  let inputValid ← input element .inputValid
  let inputData ← input element .inputData
  let outputReady ← input element .outputReady
  let reset ← input element .reset

  wire readAdvance : .bit
  wire writeAdvance : .bit
  let readCounter ← EnabledResetCounter.placeNamed "readCounter"
    (zeroPointer addressWidth) readAdvance reset
  let writeCounter ← EnabledResetCounter.placeNamed "writeCounter"
    (zeroPointer addressWidth) writeAdvance reset
  let control ← PointerControl.place
    readCounter writeCounter inputValid outputReady
  assign readAdvance control.readAdvance
  assign writeAdvance control.writeAdvance
  let storage ← RegisterBank.place
    (element := element) (addressWidth := addressWidth) (readCount := 1)
    control.writeAdvance control.writeAddress inputData
    (fun _ => control.readAddress)

  output element .outputValid control.outputValid
  output element .outputData (storage.readValue 0)
  output element .inputReady control.inputReady

noncomputable def description (element : SignalType) (addressWidth : Nat) :
    Description :=
  ModuleBuilder.build (Naming.FifoPorts.ports element)
    (construction element addressWidth)

/-! ## Exact cycle behavior -/

abbrev Entries (element : SignalType) (addressWidth : Nat) :=
  Fin (RegisterBank.entryCount addressWidth) → element.Denote

@[reducible] def pointerType (addressWidth : Nat) : SignalType :=
  .vector (addressWidth + 1) .bit

/-- The state used to describe the FIFO's exact cycle behavior. The actual
structural state is owned by the children above. -/
inductive State
  /-- The entry currently presented at the output, including its wrap bit. -/
  | readPointer
  /-- The next entry to write, including its wrap bit. -/
  | writePointer
  /-- The data currently held in every FIFO entry. -/
  | entries
deriving Enumeration

@[reducible] def stateMap (element : SignalType) (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of State fun
    | .readPointer | .writePointer => pointerType addressWidth
    | .entries => .vector (RegisterBank.entryCount addressWidth) element

def inputReady (readPointer writePointer : Pointer addressWidth) : Bool :=
  Fifo.PointerControl.inputReady readPointer writePointer

def outputValid (readPointer writePointer : Pointer addressWidth) : Bool :=
  Fifo.PointerControl.outputValid readPointer writePointer

def outputData (addressWidth : Nat) (readPointer : Pointer addressWidth)
    (entries : Entries element addressWidth) : element.Denote :=
  entries (BitVector.toIndex addressWidth
    (Fifo.PointerControl.pointerAddress readPointer))

def readAdvance (readPointer writePointer : Pointer addressWidth)
    (ready : Bool) : Bool :=
  Fifo.PointerControl.readAdvance readPointer writePointer ready

def writeAdvance (readPointer writePointer : Pointer addressWidth)
    (valid : Bool) : Bool :=
  Fifo.PointerControl.writeAdvance readPointer writePointer valid

def nextReadPointer (addressWidth : Nat) (reset ready : Bool)
    (readPointer writePointer : Pointer addressWidth) : Pointer addressWidth :=
  EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
    (readAdvance readPointer writePointer ready) reset readPointer

def nextWritePointer (addressWidth : Nat) (reset valid : Bool)
    (readPointer writePointer : Pointer addressWidth) : Pointer addressWidth :=
  EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
    (writeAdvance readPointer writePointer valid) reset writePointer

def nextEntries (addressWidth : Nat) (valid : Bool) (data : element.Denote)
    (readPointer writePointer : Pointer addressWidth)
    (entries : Entries element addressWidth) : Entries element addressWidth :=
  RegisterBank.nextEntries addressWidth
    (writeAdvance readPointer writePointer valid)
    (Fifo.PointerControl.pointerAddress writePointer) data entries

def stateRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.CycleStateRule (ports element) (stateMap element addressWidth) where
  readsInputs := .all (inputMap element)
  target inputs state := fun
        | .readPointer => nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
            (state .readPointer) (state .writePointer)
        | .writePointer => nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
            (state .readPointer) (state .writePointer)
        | .entries => nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
            (state .readPointer) (state .writePointer) (state .entries)

module_cycle_contract cycleContract (element : SignalType) (addressWidth : Nat)
    for ports element where
  state := stateMap element addressWidth
  -- Keep the two interface directions independently schedulable. In
  -- particular, observing the forward channel must not require outputReady,
  -- and observing inputReady must not require inputValid.
  output_rule forward where
    reads := []
    writes := {
      outputValid := Fifo.outputValid (state .readPointer) (state .writePointer),
      outputData :=
        Fifo.outputData addressWidth (state .readPointer) (state .entries) }
  output_rule ready where
    reads := []
    writes := {
      inputReady := Fifo.inputReady (state .readPointer) (state .writePointer) }
  state_rule := stateRule element addressWidth

/-! ## Contract-facing laws -/

section AllowedStep

variable {element : SignalType} {addressWidth : Nat}
  {step : (cycleContract element addressWidth).Step}
  (allowed : (cycleContract element addressWidth).Allows step)

include allowed

/-- The forward channel is determined entirely by the current FIFO state. -/
theorem forward_of_allowed :
    step.outputs .outputValid =
        Fifo.outputValid (step.currentState .readPointer)
          (step.currentState .writePointer) ∧
      step.outputs .outputData =
        Fifo.outputData addressWidth (step.currentState .readPointer)
          (step.currentState .entries) :=
  (forwardRule_holds_iff element addressWidth
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward)

theorem next_readPointer_of_allowed :
    step.nextState .readPointer =
      nextReadPointer addressWidth (step.inputs .reset)
        (step.inputs .outputReady) (step.currentState .readPointer)
        (step.currentState .writePointer) := by
  rw [allowed.2]
  rfl

theorem next_writePointer_of_allowed :
    step.nextState .writePointer =
      nextWritePointer addressWidth (step.inputs .reset)
        (step.inputs .inputValid) (step.currentState .readPointer)
        (step.currentState .writePointer) := by
  rw [allowed.2]
  rfl

theorem next_entries_of_allowed :
    step.nextState .entries =
      nextEntries addressWidth (step.inputs .inputValid) (step.inputs .inputData)
        (step.currentState .readPointer) (step.currentState .writePointer)
        (step.currentState .entries) := by
  rw [allowed.2]
  rfl

end AllowedStep

@[simp] theorem stateRule_apply_readPointer (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth).apply inputs state .readPointer =
      nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
        (state .readPointer) (state .writePointer) := by rfl

@[simp] theorem stateRule_apply_writePointer (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth).apply inputs state .writePointer =
      nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
        (state .readPointer) (state .writePointer) := by rfl

@[simp] theorem stateRule_apply_entries (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth).apply inputs state .entries =
      nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
        (state .readPointer) (state .writePointer) (state .entries) := by rfl

theorem reset_readPointer (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (reset : inputs .reset = true) :
    (stateRule element addressWidth).apply inputs state .readPointer =
      zeroPointer addressWidth := by
  rw [stateRule_apply_readPointer, nextReadPointer,
    EnabledResetCounter.nextValue, reset]
  rfl

theorem reset_writePointer (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (reset : inputs .reset = true) :
    (stateRule element addressWidth).apply inputs state .writePointer =
      zeroPointer addressWidth := by
  rw [stateRule_apply_writePointer, nextWritePointer,
    EnabledResetCounter.nextValue, reset]
  rfl

theorem equalPointers_empty (pointer : Pointer addressWidth) :
    Fifo.outputValid pointer pointer = false ∧
      Fifo.inputReady pointer pointer = true := by
  have empty := (Fifo.PointerControl.empty_eq_true_iff pointer pointer).mpr rfl
  simp [Fifo.outputValid, Fifo.inputReady, Fifo.PointerControl.outputValid,
    Fifo.PointerControl.inputReady, empty,
    Fifo.PointerControl.empty_implies_not_full pointer pointer empty]

/-! Reset is synchronous: current outputs and the ordinary accepted bank write
are determined from the pre-edge state. Reset has priority in both pointer
updates, so the state observed after that edge is empty without clearing the
entry array. -/

theorem empty_after_reset (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (reset : inputs .reset = true) :
    let nextState := (stateRule element addressWidth).apply inputs state
    Fifo.outputValid (nextState .readPointer) (nextState .writePointer) = false ∧
      Fifo.inputReady (nextState .readPointer) (nextState .writePointer) = true := by
  dsimp
  rw [reset_readPointer element addressWidth inputs state reset,
    reset_writePointer element addressWidth inputs state reset]
  exact equalPointers_empty (zeroPointer addressWidth)

theorem retained_entries_of_blocked_write (addressWidth : Nat)
    (valid : Bool) (data : element.Denote)
    (readPointer writePointer : Pointer addressWidth)
    (entries : Entries element addressWidth)
    (blocked : writeAdvance readPointer writePointer valid = false) :
    nextEntries addressWidth valid data readPointer writePointer entries = entries := by
  unfold nextEntries
  rw [blocked]
  exact RegisterBank.nextEntries_disabled _ _ _ _

theorem written_entry_of_accepted_input (addressWidth : Nat)
    (valid : Bool) (data : element.Denote)
    (readPointer writePointer : Pointer addressWidth)
    (entries : Entries element addressWidth)
    (accepted : writeAdvance readPointer writePointer valid = true) :
    nextEntries addressWidth valid data readPointer writePointer entries
      (BitVector.toIndex addressWidth
        (Fifo.PointerControl.pointerAddress writePointer)) = data := by
  unfold nextEntries
  rw [accepted]
  exact RegisterBank.nextEntries_selected _ _ _ _

/-! ## Logical queue view -/

namespace Properties

abbrev Word (element : SignalType) := element.Denote

abbrev ContractState (element : SignalType) (addressWidth : Nat) :=
  (cycleContract element addressWidth).state.Values

def capacity (addressWidth : Nat) : Nat := BitVector.cardinality addressWidth

def pointerModulus (addressWidth : Nat) : Nat :=
  BitVector.cardinality (addressWidth + 1)

theorem capacity_positive (addressWidth : Nat) : 0 < capacity addressWidth := by
  rw [capacity, BitVector.cardinality_eq_pow]
  exact Nat.two_pow_pos addressWidth

instance capacityNeZero (addressWidth : Nat) : NeZero (capacity addressWidth) :=
  ⟨Nat.ne_of_gt (capacity_positive addressWidth)⟩

def pointerValue (addressWidth : Nat) (pointer : Pointer addressWidth) : Nat :=
  BitVector.toNat (addressWidth + 1) pointer

def occupancy (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) : Nat :=
  CircularBuffer.distance (pointerModulus addressWidth)
    (pointerValue addressWidth readPointer)
    (pointerValue addressWidth writePointer)

def Invariant (addressWidth : Nat)
    (state : ContractState element addressWidth) : Prop :=
  occupancy addressWidth (state .readPointer) (state .writePointer) ≤
    capacity addressWidth

def entryIndex (addressWidth : Nat) (pointer : Pointer addressWidth) :
    Fin (capacity addressWidth) :=
  Fin.ofNat (capacity addressWidth) (pointerValue addressWidth pointer)

def contentsOf (addressWidth : Nat) (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth) : List (Word element) :=
  CircularBuffer.values (capacity addressWidth) entries
    (entryIndex addressWidth readPointer)
    (occupancy addressWidth readPointer writePointer)

def contents (addressWidth : Nat) (state : ContractState element addressWidth) :
    List (Word element) :=
  contentsOf addressWidth (state .entries) (state .readPointer)
    (state .writePointer)

end Properties

end Silean.Modules.Fifo
