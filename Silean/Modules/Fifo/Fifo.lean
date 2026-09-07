import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledResetCounter.EnabledResetCounter
import Silean.Interfaces.FifoPorts
import Silean.Modules.Fifo.FifoPointerControl
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Naming.FifoPortsNaming

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo

/-- A FIFO with `2 ^ addressWidth` entries of `element`, built from a register
bank with read and write pointers.

The extra high bit in each pointer distinguishes a full buffer from an empty
one when their address bits are equal. Reset is synchronous; invalid storage
contents do not need to be cleared. -/

abbrev Pointer (addressWidth : Nat) :=
  EnabledResetCounter.Value (addressWidth + 1)

/-- Both counters start at the first entry, making the FIFO empty. -/
def zeroPointer (addressWidth : Nat) : Pointer addressWidth := fun _ => false

end Silean.Modules.Fifo

namespace Silean.Modules

open Silean
open Silean.Authoring
open Silean.Interfaces.Fifo

/-! ## Hardware structure -/

module_design Fifo (element : SignalType) (addressWidth : Nat) where
  boundary (Interfaces.Fifo.ports element)
    (naming := Naming.FifoPorts.ports element)
  instances {
    -- Tracks the entry currently presented at the output.
    readCounter :=
      EnabledResetCounter.design (addressWidth + 1)
        (Fifo.zeroPointer addressWidth),
    -- Tracks the entry where the next accepted input will be stored.
    writeCounter :=
      EnabledResetCounter.design (addressWidth + 1)
        (Fifo.zeroPointer addressWidth),
    -- Derives handshake decisions and storage addresses from the pointers.
    control :=
      Fifo.PointerControl.design addressWidth,
    -- Holds all FIFO data entries and provides the asynchronous read port.
    storage := RegisterBank.design element addressWidth 1 }
  wiring {
    outputs {
      .outputValid := control.outputValid,
      .outputData := storage[.readValue 0],
      .inputReady := control.inputReady }
    instance (.readCounter) {
      .enable := control.readAdvance,
      .reset := input.reset }
    instance (.writeCounter) {
      .enable := control.writeAdvance,
      .reset := input.reset }
    instance (.control) {
      .readPointer := readCounter.value,
      .writePointer := writeCounter.value,
      .inputValid := input.inputValid,
      .outputReady := input.outputReady }
    instance (.storage) {
      .writeEnable := control.writeAdvance,
      .writeAddress := control.writeAddress,
      .writeValue := input.inputData,
      .readAddress 0 := control.readAddress }
  }

namespace Fifo.Naming

open Silean.Naming

/-- Attach authored payload names to the FIFO boundary and recursively to its
storage hierarchy without changing the canonical FIFO structure. -/
def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Fifo.moduleStructure element addressWidth) := by
  unfold Fifo.moduleStructure
  exact .composite
    ⟨"Fifo", "", [.signalType element, .natural addressWidth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming element elementNaming)
    (instanceNames element addressWidth)
    (fun
      | .readCounter => EnabledResetCounter.naming (addressWidth + 1)
          (Fifo.zeroPointer addressWidth)
      | .writeCounter => EnabledResetCounter.naming (addressWidth + 1)
          (Fifo.zeroPointer addressWidth)
      | .control => Fifo.PointerControl.naming addressWidth
      | .storage => RegisterBank.Naming.namingWith element addressWidth 1
          elementNaming)

end Fifo.Naming

end Silean.Modules

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo
open Contracts.Cycle.Certification.Layer

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
      outputValid := outputValid (state .readPointer) (state .writePointer),
      outputData := outputData addressWidth (state .readPointer) (state .entries) }
  output_rule ready where
    reads := []
    writes := {
      inputReady := inputReady (state .readPointer) (state .writePointer) }
  state_rule := stateRule element addressWidth

/-! ## Contract-facing laws -/

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
    outputValid pointer pointer = false ∧ inputReady pointer pointer = true := by
  have empty := (Fifo.PointerControl.empty_eq_true_iff pointer pointer).mpr rfl
  simp [outputValid, inputReady, Fifo.PointerControl.outputValid,
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
    outputValid (nextState .readPointer) (nextState .writePointer) = false ∧
      inputReady (nextState .readPointer) (nextState .writePointer) = true := by
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

end Silean.Modules.Fifo
