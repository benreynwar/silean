import Silean.Modules.Fifo.CircularBuffer
import Silean.Modules.Fifo.Fifo

namespace Silean.Modules.Fifo.Properties

open Silean Silean.Interfaces.Fifo

/-! Queue-oriented properties of the FIFO's exact cycle contract. The FIFO is
built from a register bank controlled by read and write pointers. These lemmas
support the abstract FIFO refinement behind `FifoFifoTheorems`. -/

abbrev Word (element : SignalType) := element.Denote
abbrev ContractState (element : SignalType) (addressWidth : Nat) :=
  (cycleContract element addressWidth).state.Values

def capacity (addressWidth : Nat) : Nat := BitVector.cardinality addressWidth

def pointerModulus (addressWidth : Nat) : Nat :=
  BitVector.cardinality (addressWidth + 1)

@[simp] private theorem pointerModulus_eq (addressWidth : Nat) :
    pointerModulus addressWidth = capacity addressWidth + capacity addressWidth := rfl

theorem capacity_positive (addressWidth : Nat) : 0 < capacity addressWidth := by
  rw [capacity, BitVector.cardinality_eq_pow]
  exact Nat.two_pow_pos addressWidth

private theorem pointerModulus_positive (addressWidth : Nat) :
    0 < pointerModulus addressWidth := by
  rw [pointerModulus_eq]
  exact Nat.add_pos_left (capacity_positive addressWidth) _

instance capacityNeZero (addressWidth : Nat) : NeZero (capacity addressWidth) :=
  ⟨Nat.ne_of_gt (capacity_positive addressWidth)⟩

def pointerValue (addressWidth : Nat) (pointer : Pointer addressWidth) : Nat :=
  BitVector.toNat (addressWidth + 1) pointer

private theorem pointerValue_lt (addressWidth : Nat) (pointer : Pointer addressWidth) :
    pointerValue addressWidth pointer < pointerModulus addressWidth :=
  BitVector.toNat_lt_cardinality _ _

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

@[simp] theorem contents_length (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    (contents addressWidth state).length =
      occupancy addressWidth (state .readPointer) (state .writePointer) := by
  exact CircularBuffer.values_length _ _ _ _

theorem contents_bounded (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (invariant : Invariant addressWidth state) :
    (contents addressWidth state).length ≤ capacity addressWidth := by
  rw [contents_length]
  exact invariant

private theorem pointerValue_decompose (addressWidth : Nat)
    (pointer : Pointer addressWidth) :
    pointerValue addressWidth pointer =
      (if Fifo.PointerControl.pointerWrap pointer then capacity addressWidth else 0) +
        BitVector.toNat addressWidth
          (Fifo.PointerControl.pointerAddress pointer) := by
  rfl

private theorem entryIndex_eq_pointerAddress (addressWidth : Nat)
    (pointer : Pointer addressWidth) :
    entryIndex addressWidth pointer =
      BitVector.toIndex addressWidth
        (Fifo.PointerControl.pointerAddress pointer) := by
  apply Fin.ext
  change (pointerValue addressWidth pointer) % capacity addressWidth = _
  rw [BitVector.toIndex_val, pointerValue_decompose]
  have bound := BitVector.toNat_lt_cardinality addressWidth
    (Fifo.PointerControl.pointerAddress pointer)
  rw [BitVector.cardinality_eq_pow] at bound
  cases wrap : Fifo.PointerControl.pointerWrap pointer <;>
    simp [capacity] <;>
    exact Nat.mod_eq_of_lt bound

private theorem entryIndex_eq_advance (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) :
    entryIndex addressWidth writePointer =
      CircularBuffer.advance (capacity addressWidth)
        (entryIndex addressWidth readPointer)
        (occupancy addressWidth readPointer writePointer) := by
  symm
  apply CircularBuffer.advance_distance_double
  · simpa [pointerModulus_eq] using pointerValue_lt addressWidth readPointer
  · simpa [pointerModulus_eq] using pointerValue_lt addressWidth writePointer

theorem occupancy_eq_zero_iff (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) :
    occupancy addressWidth readPointer writePointer = 0 ↔
      readPointer = writePointer := by
  unfold occupancy
  rw [CircularBuffer.distance_eq_zero_iff]
  · exact ⟨fun equal => BitVector.toNat_injective _ equal,
      fun equal => congrArg (pointerValue addressWidth) equal⟩
  · exact pointerModulus_positive addressWidth
  · exact pointerValue_lt addressWidth readPointer
  · exact pointerValue_lt addressWidth writePointer

theorem occupancy_eq_capacity_iff_full (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth)
    (valid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth) :
    occupancy addressWidth readPointer writePointer = capacity addressWidth ↔
      Fifo.PointerControl.full readPointer writePointer = true := by
  let readAddress := BitVector.toNat addressWidth
    (Fifo.PointerControl.pointerAddress readPointer)
  let writeAddress := BitVector.toNat addressWidth
    (Fifo.PointerControl.pointerAddress writePointer)
  have readAddressBound : readAddress < capacity addressWidth :=
    BitVector.toNat_lt_cardinality _ _
  have writeAddressBound : writeAddress < capacity addressWidth :=
    BitVector.toNat_lt_cardinality _ _
  have capacityPositive := capacity_positive addressWidth
  have addressEquality :
      Fifo.PointerControl.pointerAddress readPointer =
          Fifo.PointerControl.pointerAddress writePointer ↔
        readAddress = writeAddress := by
    constructor
    · exact fun equal => congrArg (BitVector.toNat addressWidth) equal
    · intro equal
      apply BitVector.toNat_injective addressWidth
      simpa [readAddress, writeAddress] using equal
  rw [Fifo.PointerControl.full_eq_true_iff, addressEquality]
  unfold occupancy at valid ⊢
  rw [pointerModulus_eq, pointerValue_decompose, pointerValue_decompose]
    at valid ⊢
  cases readWrap : Fifo.PointerControl.pointerWrap readPointer <;>
    cases writeWrap : Fifo.PointerControl.pointerWrap writePointer
  all_goals
    simp [readWrap, writeWrap, CircularBuffer.distance] at valid ⊢
    split <;> simp_all <;> omega

theorem occupancy_eq_zero_iff_empty (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) :
    occupancy addressWidth readPointer writePointer = 0 ↔
      Fifo.PointerControl.empty readPointer writePointer = true := by
  rw [occupancy_eq_zero_iff,
    Fifo.PointerControl.empty_eq_true_iff]

theorem contents_eq_nil_iff_empty (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    contents addressWidth state = [] ↔
      Fifo.PointerControl.empty (state .readPointer) (state .writePointer) = true := by
  rw [← occupancy_eq_zero_iff_empty]
  constructor
  · intro empty
    have lengths := congrArg List.length empty
    rw [contents_length] at lengths
    simpa using lengths
  · intro zero
    apply List.eq_nil_of_length_eq_zero
    rw [contents_length, zero]

theorem contents_length_eq_capacity_iff_full (addressWidth : Nat)
    (state : ContractState element addressWidth) (valid : Invariant addressWidth state) :
    (contents addressWidth state).length = capacity addressWidth ↔
      Fifo.PointerControl.full (state .readPointer) (state .writePointer) = true := by
  rw [contents_length]
  exact occupancy_eq_capacity_iff_full addressWidth (state .readPointer)
    (state .writePointer) valid

theorem outputValid_eq_contents_nonempty (addressWidth : Nat)
    (state : ContractState element addressWidth) :
    Fifo.outputValid (state .readPointer) (state .writePointer) =
      !(contents addressWidth state).isEmpty := by
  rw [Bool.eq_iff_iff]
  simp [Fifo.outputValid, Fifo.PointerControl.outputValid,
    contents_eq_nil_iff_empty]

theorem inputReady_eq_contents_below_capacity (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (valid : Invariant addressWidth state) :
    Fifo.inputReady (state .readPointer) (state .writePointer) =
      decide ((contents addressWidth state).length < capacity addressWidth) := by
  have fullIff := contents_length_eq_capacity_iff_full addressWidth state valid
  cases fullEq : Fifo.PointerControl.full (state .readPointer) (state .writePointer)
  · have notEqual : (contents addressWidth state).length ≠ capacity addressWidth := by
      intro equal
      have := fullIff.mp equal
      simp [fullEq] at this
    have below : (contents addressWidth state).length < capacity addressWidth := by
      have bounded := contents_bounded addressWidth state valid
      omega
    rw [Fifo.inputReady, Fifo.PointerControl.inputReady, fullEq]
    have decided : decide ((contents addressWidth state).length <
        capacity addressWidth) = true := decide_eq_true_iff.mpr below
    exact decided.symm
  · have equal : (contents addressWidth state).length = capacity addressWidth :=
      fullIff.mpr fullEq
    rw [Fifo.inputReady, Fifo.PointerControl.inputReady, fullEq]
    have notBelow : ¬(contents addressWidth state).length < capacity addressWidth := by
      omega
    have decided : decide ((contents addressWidth state).length <
        capacity addressWidth) = false := decide_eq_false_iff_not.mpr notBelow
    exact decided.symm

private theorem pointerValue_nextRead_of_notReset (addressWidth : Nat)
    (ready : Bool) (readPointer writePointer : Pointer addressWidth) :
    pointerValue addressWidth
        (nextReadPointer addressWidth false ready readPointer writePointer) =
      if readAdvance readPointer writePointer ready then
        (pointerValue addressWidth readPointer + 1) % pointerModulus addressWidth
      else pointerValue addressWidth readPointer := by
  unfold nextReadPointer EnabledResetCounter.nextValue pointerValue
  cases advance : readAdvance readPointer writePointer ready <;>
    simp [Increment.incrementValue_toNat, pointerModulus]

private theorem pointerValue_nextWrite_of_notReset (addressWidth : Nat)
    (valid : Bool) (readPointer writePointer : Pointer addressWidth) :
    pointerValue addressWidth
        (nextWritePointer addressWidth false valid readPointer writePointer) =
      if writeAdvance readPointer writePointer valid then
        (pointerValue addressWidth writePointer + 1) % pointerModulus addressWidth
      else pointerValue addressWidth writePointer := by
  unfold nextWritePointer EnabledResetCounter.nextValue pointerValue
  cases advance : writeAdvance readPointer writePointer valid <;>
    simp [Increment.incrementValue_toNat, pointerModulus]

@[simp] private theorem pointerValue_zeroPointer (addressWidth : Nat) :
    pointerValue addressWidth (zeroPointer addressWidth) = 0 := by
  simp [pointerValue, zeroPointer, BitVector.toNat]

private theorem nextEntries_of_acceptedInput (addressWidth : Nat)
    (valid : Bool) (data : Word element)
    (readPointer writePointer : Pointer addressWidth)
    (entries : Entries element addressWidth)
    (accepted : writeAdvance readPointer writePointer valid = true) :
    nextEntries addressWidth valid data readPointer writePointer entries =
      CircularBuffer.write (capacity addressWidth) entries
        (entryIndex addressWidth writePointer) data := by
  unfold nextEntries
  rw [accepted, entryIndex_eq_pointerAddress]
  funext index
  unfold RegisterBank.nextEntries CircularBuffer.write
  by_cases selected : index = BitVector.toIndex addressWidth
      (Fifo.PointerControl.pointerAddress writePointer)
  · subst index
    simp
  · have decided : decide (index = BitVector.toIndex addressWidth
        (Fifo.PointerControl.pointerAddress writePointer)) = false := by
      simp [selected]
    rw [decided]
    simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i equal
      exact (selected equal).elim
    · rfl

private theorem occupancy_positive_of_readAdvance (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) (ready : Bool)
    (accepted : readAdvance readPointer writePointer ready = true) :
    0 < occupancy addressWidth readPointer writePointer := by
  have outputValid :=
    (Fifo.PointerControl.readAdvance_eq_true_iff readPointer writePointer ready).mp
      accepted |>.1
  by_cases positive : 0 < occupancy addressWidth readPointer writePointer
  · exact positive
  exfalso
  have zero : occupancy addressWidth readPointer writePointer = 0 := by omega
  have empty := (occupancy_eq_zero_iff_empty addressWidth readPointer writePointer).mp
    zero
  simp [Fifo.PointerControl.outputValid, empty] at outputValid

private theorem occupancy_lt_capacity_of_writeAdvance (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth) (validInput : Bool)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth)
    (accepted : writeAdvance readPointer writePointer validInput = true) :
    occupancy addressWidth readPointer writePointer < capacity addressWidth := by
  have inputReady :=
    (Fifo.PointerControl.writeAdvance_eq_true_iff readPointer writePointer
      validInput).mp accepted |>.2
  by_cases below : occupancy addressWidth readPointer writePointer <
      capacity addressWidth
  · exact below
  exfalso
  have equal : occupancy addressWidth readPointer writePointer =
      capacity addressWidth := by omega
  have full := (occupancy_eq_capacity_iff_full addressWidth readPointer writePointer
    stateValid).mp equal
  simp [Fifo.PointerControl.inputReady, full] at inputReady

private theorem occupancy_next_of_notReset (addressWidth : Nat)
    (readPointer writePointer : Pointer addressWidth)
    (ready validInput : Bool)
    (stateValid : occupancy addressWidth readPointer writePointer ≤
      capacity addressWidth) :
    occupancy addressWidth
        (nextReadPointer addressWidth false ready readPointer writePointer)
        (nextWritePointer addressWidth false validInput readPointer writePointer) =
      occupancy addressWidth readPointer writePointer +
          (if writeAdvance readPointer writePointer validInput then 1 else 0) -
        (if readAdvance readPointer writePointer ready then 1 else 0) := by
  let count := occupancy addressWidth readPointer writePointer
  have readBound := pointerValue_lt addressWidth readPointer
  have writeBound := pointerValue_lt addressWidth writePointer
  have modulusPositive := pointerModulus_positive addressWidth
  unfold occupancy
  rw [pointerValue_nextRead_of_notReset,
    pointerValue_nextWrite_of_notReset]
  cases readAccepted : readAdvance readPointer writePointer ready <;>
    cases writeAccepted : writeAdvance readPointer writePointer validInput
  · simp
  · simp
    apply CircularBuffer.distance_advance_write modulusPositive readBound writeBound
      rfl
    have below := occupancy_lt_capacity_of_writeAdvance addressWidth readPointer
      writePointer validInput stateValid writeAccepted
    unfold occupancy at below
    rw [pointerModulus_eq]
    rw [pointerModulus_eq] at below
    have capacityPositive := capacity_positive addressWidth
    omega
  · simp
    apply CircularBuffer.distance_advance_read modulusPositive readBound writeBound rfl
    exact occupancy_positive_of_readAdvance addressWidth readPointer writePointer
      ready readAccepted
  · simp
    exact CircularBuffer.distance_advance_both modulusPositive readBound writeBound

private theorem entryIndex_nextRead_of_notReset (addressWidth : Nat)
    (ready : Bool) (readPointer writePointer : Pointer addressWidth) :
    entryIndex addressWidth
        (nextReadPointer addressWidth false ready readPointer writePointer) =
      if readAdvance readPointer writePointer ready then
        CircularBuffer.advance (capacity addressWidth)
          (entryIndex addressWidth readPointer) 1
      else entryIndex addressWidth readPointer := by
  apply Fin.ext
  unfold entryIndex CircularBuffer.advance
  rw [Fin.val_ofNat]
  rw [pointerValue_nextRead_of_notReset]
  cases accepted : readAdvance readPointer writePointer ready
  · simp
  · simp only [if_true, Fin.val_add, Fin.val_ofNat]
    rw [pointerModulus_eq]
    have capacityPositive := capacity_positive addressWidth
    have pointerBound := pointerValue_lt addressWidth readPointer
    rw [pointerModulus_eq] at pointerBound
    have divides : capacity addressWidth ∣
        capacity addressWidth + capacity addressWidth := by
      exact ⟨2, by omega⟩
    rw [Nat.mod_mod_of_dvd _ divides]
    simp [Nat.mod_add_mod]

private theorem contentsOf_positive (addressWidth : Nat)
    (entries : Entries element addressWidth)
    (readPointer writePointer : Pointer addressWidth)
    (positive : 0 < occupancy addressWidth readPointer writePointer) :
    contentsOf addressWidth entries readPointer writePointer =
      outputData addressWidth readPointer entries ::
        CircularBuffer.values (capacity addressWidth) entries
          (CircularBuffer.advance (capacity addressWidth)
            (entryIndex addressWidth readPointer) 1)
          (occupancy addressWidth readPointer writePointer - 1) := by
  unfold contentsOf
  cases count : occupancy addressWidth readPointer writePointer with
  | zero => omega
  | succ count =>
      simp only [CircularBuffer.values_succ, Nat.add_sub_cancel]
      congr 1
      exact congrArg entries (entryIndex_eq_pointerAddress addressWidth readPointer)

theorem outputData_eq_contents_head (addressWidth : Nat)
    (state : ContractState element addressWidth) (head : Word element)
    (tail : List (Word element))
    (equal : contents addressWidth state = head :: tail) :
    Fifo.outputData addressWidth (state .readPointer) (state .entries) = head := by
  have positive : 0 < occupancy addressWidth
      (state .readPointer) (state .writePointer) := by
    have lengths := congrArg List.length equal
    rw [contents_length] at lengths
    simp at lengths
    omega
  have expanded := contentsOf_positive addressWidth (state .entries)
    (state .readPointer) (state .writePointer) positive
  change contents addressWidth state = _ at expanded
  rw [equal] at expanded
  exact List.cons.inj expanded |>.1.symm

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
          (nextWritePointer addressWidth false validInput readPointer writePointer) := by
  have nextOccupancy := occupancy_next_of_notReset addressWidth readPointer
    writePointer ready validInput stateValid
  have nextIndex := entryIndex_nextRead_of_notReset addressWidth ready readPointer
    writePointer
  cases readAccepted : readAdvance readPointer writePointer ready <;>
    cases writeAccepted : writeAdvance readPointer writePointer validInput
  · have retained := retained_entries_of_blocked_write addressWidth validInput data
      readPointer writePointer entries writeAccepted
    simp [readAccepted, writeAccepted] at nextOccupancy nextIndex ⊢
    unfold contentsOf
    rw [retained, nextIndex, nextOccupancy]
  · have written := nextEntries_of_acceptedInput addressWidth validInput data
      readPointer writePointer entries writeAccepted
    have below := occupancy_lt_capacity_of_writeAdvance addressWidth readPointer
      writePointer validInput stateValid writeAccepted
    simp [readAccepted, writeAccepted] at nextOccupancy nextIndex ⊢
    unfold contentsOf
    rw [written, nextIndex, nextOccupancy,
      entryIndex_eq_advance addressWidth readPointer writePointer]
    exact (CircularBuffer.values_write_tail (capacity addressWidth) entries
      (entryIndex addressWidth readPointer) data
      (occupancy addressWidth readPointer writePointer) below).symm
  · have retained := retained_entries_of_blocked_write addressWidth validInput data
      readPointer writePointer entries writeAccepted
    have positive := occupancy_positive_of_readAdvance addressWidth readPointer
      writePointer ready readAccepted
    have current := contentsOf_positive addressWidth entries readPointer
      writePointer positive
    simp [readAccepted, writeAccepted] at nextOccupancy nextIndex ⊢
    rw [current]
    unfold contentsOf
    rw [retained, nextIndex, nextOccupancy]
  · have written := nextEntries_of_acceptedInput addressWidth validInput data
      readPointer writePointer entries writeAccepted
    have positive := occupancy_positive_of_readAdvance addressWidth readPointer
      writePointer ready readAccepted
    have below := occupancy_lt_capacity_of_writeAdvance addressWidth readPointer
      writePointer validInput stateValid writeAccepted
    have current := contentsOf_positive addressWidth entries readPointer
      writePointer positive
    simp [readAccepted, writeAccepted] at nextOccupancy nextIndex ⊢
    rw [current]
    unfold contentsOf
    rw [written, nextIndex, nextOccupancy,
      entryIndex_eq_advance addressWidth readPointer writePointer]
    simp only [List.cons_append, List.cons.injEq, true_and]
    rw [← CircularBuffer.values_tail]
    exact (CircularBuffer.values_write_after_head (capacity addressWidth) entries
      (entryIndex addressWidth readPointer) data
      (occupancy addressWidth readPointer writePointer) positive below).symm

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
      contentsOf addressWidth entries readPointer writePointer := by
  have law := contentsOf_next_of_notReset addressWidth entries readPointer
    writePointer ready validInput data stateValid
  simpa [noRead, noWrite] using law.symm

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
      contentsOf addressWidth entries readPointer writePointer ++ [data] := by
  have law := contentsOf_next_of_notReset addressWidth entries readPointer
    writePointer ready validInput data stateValid
  simpa [noRead, writeAccepted] using law.symm

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
          (nextWritePointer addressWidth false validInput readPointer writePointer) := by
  have law := contentsOf_next_of_notReset addressWidth entries readPointer
    writePointer ready validInput data stateValid
  simpa [readAccepted, noWrite] using law

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
          (nextWritePointer addressWidth false validInput readPointer writePointer) := by
  have law := contentsOf_next_of_notReset addressWidth entries readPointer
    writePointer ready validInput data stateValid
  simpa [readAccepted, writeAccepted] using law

namespace Evaluation

/-! Contract-evaluation facts used by the private FIFO refinement proof. -/

theorem evaluated_outputs (element : SignalType) (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (inputs : (ports element).inputs.Values) :
    let outputs := ((cycleContract element addressWidth).evaluate inputs state).1
    outputs .outputValid = outputValid (state .readPointer) (state .writePointer) ∧
      outputs .outputData = outputData addressWidth (state .readPointer)
        (state .entries) ∧
      outputs .inputReady = inputReady (state .readPointer) (state .writePointer) := by
  intro outputs
  have allowed := (cycleContract element addressWidth).evaluateStep_allowed
    inputs state
  exact ⟨((forwardRule_holds_iff element addressWidth _ _ outputs).mp
      (allowed.1 .forward)).1,
    ((forwardRule_holds_iff element addressWidth _ _ outputs).mp
      (allowed.1 .forward)).2,
    (readyRule_holds_iff element addressWidth _ _ outputs).mp
      (allowed.1 .ready)⟩

@[simp] theorem evaluated_next_readPointer (element : SignalType)
    (addressWidth : Nat) (state : ContractState element addressWidth)
    (inputs : (ports element).inputs.Values) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .readPointer =
      nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
        (state .readPointer) (state .writePointer) := by rfl

@[simp] theorem evaluated_next_writePointer (element : SignalType)
    (addressWidth : Nat) (state : ContractState element addressWidth)
    (inputs : (ports element).inputs.Values) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .writePointer =
      nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
        (state .readPointer) (state .writePointer) := by rfl

@[simp] theorem evaluated_next_entries (element : SignalType)
    (addressWidth : Nat) (state : ContractState element addressWidth)
    (inputs : (ports element).inputs.Values) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .entries =
      nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
        (state .readPointer) (state .writePointer) (state .entries) := by rfl

theorem next_preserves_invariant (element : SignalType) (addressWidth : Nat)
    (state : ContractState element addressWidth)
    (inputs : (ports element).inputs.Values)
    (valid : Invariant addressWidth state) :
    Invariant addressWidth
      ((cycleContract element addressWidth).evaluate inputs state).2 := by
  unfold Invariant
  change occupancy addressWidth (state .readPointer) (state .writePointer) ≤
    capacity addressWidth at valid
  cases reset : inputs .reset
  · rw [evaluated_next_readPointer, evaluated_next_writePointer]
    simp only [reset]
    rw [occupancy_next_of_notReset addressWidth (state .readPointer)
      (state .writePointer) (inputs .outputReady) (inputs .inputValid) valid]
    cases readAccepted : readAdvance (state .readPointer) (state .writePointer)
        (inputs .outputReady) <;>
      cases writeAccepted : writeAdvance (state .readPointer) (state .writePointer)
        (inputs .inputValid)
    · simpa [readAccepted, writeAccepted] using valid
    · have below := occupancy_lt_capacity_of_writeAdvance addressWidth
        (state .readPointer) (state .writePointer) (inputs .inputValid) valid writeAccepted
      simp
      omega
    · simp
      omega
    · simpa [readAccepted, writeAccepted] using valid
  · rw [evaluated_next_readPointer, evaluated_next_writePointer]
    simp only [reset, nextReadPointer, nextWritePointer,
      EnabledResetCounter.nextValue]
    simp [occupancy, pointerValue_zeroPointer, CircularBuffer.distance]

end Evaluation

end Silean.Modules.Fifo.Properties
