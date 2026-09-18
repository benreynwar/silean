import RV32I.Execution

namespace RV32I

namespace SequentialMemory

abbrev Byte := BitVec 8

/-- Byte ordering selected by an execution environment. -/
inductive Endianness where
  | little
  | big
  deriving DecidableEq, Repr

/-- Abstract array-like memory state.

The carrier is supplied by a client. These operations and laws do not choose
an array, function, map, or any other concrete representation. -/
structure ByteStorage (Memory : Type) where
  readByte : Memory → Address → Byte
  writeByte : Memory → Address → Byte → Memory
  read_write_same (memory : Memory) (address : Address) (value : Byte) :
    readByte (writeByte memory address value) address = value
  read_write_other (memory : Memory) (writeAddress readAddress : Address)
      (value : Byte) (different : readAddress ≠ writeAddress) :
    readByte (writeByte memory writeAddress value) readAddress =
      readByte memory readAddress

variable {Memory : Type}

/-- Address of one byte within an access in this optional total-memory
profile. Offsets wrap modulo `2^32`. This is a deliberate EEI interpretation,
not a rule imposed on every architectural access or on Sail physical memory. -/
def byteAddress (address : Address) (offset : Nat) : Address :=
  address + BitVec.ofNat 32 offset

@[simp] theorem byteAddress_zero (address : Address) :
    byteAddress address 0 = address := by
  simp [byteAddress]

example : byteAddress 0xffffffff 1 = (0 : Address) := by
  native_decide

@[simp] theorem ByteStorage.readByte_writeByte_same
    (storage : ByteStorage Memory) (memory : Memory)
    (address : Address) (value : Byte) :
    storage.readByte (storage.writeByte memory address value) address = value :=
  storage.read_write_same memory address value

@[simp] theorem ByteStorage.readByte_writeByte_other
    (storage : ByteStorage Memory) (memory : Memory)
    (writeAddress readAddress : Address) (value : Byte)
    (different : readAddress ≠ writeAddress) :
    storage.readByte (storage.writeByte memory writeAddress value) readAddress =
      storage.readByte memory readAddress :=
  storage.read_write_other memory writeAddress readAddress value different

/-- Read a width-indexed value using the selected byte order. -/
def readValue (storage : ByteStorage Memory) (endianness : Endianness)
    (memory : Memory) (address : Address) :
    (width : AccessWidth) → AccessValue width
  | .byte => storage.readByte memory address
  | .half =>
      match endianness with
      | .little =>
          storage.readByte memory (byteAddress address 1) ++
            storage.readByte memory address
      | .big =>
          storage.readByte memory address ++
            storage.readByte memory (byteAddress address 1)
  | .word =>
      match endianness with
      | .little =>
          storage.readByte memory (byteAddress address 3) ++
          storage.readByte memory (byteAddress address 2) ++
          storage.readByte memory (byteAddress address 1) ++
          storage.readByte memory address
      | .big =>
          storage.readByte memory address ++
          storage.readByte memory (byteAddress address 1) ++
          storage.readByte memory (byteAddress address 2) ++
          storage.readByte memory (byteAddress address 3)

theorem readValue_little_word
    (storage : ByteStorage Memory) (memory : Memory) (address : Address) :
    readValue storage .little memory address .word =
      storage.readByte memory (byteAddress address 3) ++
      storage.readByte memory (byteAddress address 2) ++
      storage.readByte memory (byteAddress address 1) ++
      storage.readByte memory address := by
  rfl

theorem readValue_big_word
    (storage : ByteStorage Memory) (memory : Memory) (address : Address) :
    readValue storage .big memory address .word =
      storage.readByte memory address ++
      storage.readByte memory (byteAddress address 1) ++
      storage.readByte memory (byteAddress address 2) ++
      storage.readByte memory (byteAddress address 3) := by
  rfl

/-- Read one fixed-width RV32 instruction from its four bytes.

RISC-V instruction parcels are always stored little-endian, independently of
the endianness selected by the EEI for explicit data loads and stores. -/
def readInstruction (storage : ByteStorage Memory) (memory : Memory)
    (address : Address) : Word :=
  readValue storage .little memory address .word

theorem readInstruction_eq_bytes
    (storage : ByteStorage Memory) (memory : Memory) (address : Address) :
    readInstruction storage memory address =
      storage.readByte memory (byteAddress address 3) ++
      storage.readByte memory (byteAddress address 2) ++
      storage.readByte memory (byteAddress address 1) ++
      storage.readByte memory address := by
  rfl

/-- Write a width-indexed value as byte updates in increasing address-offset
order. Endianness selects which value byte is assigned to each offset. -/
def writeValue (storage : ByteStorage Memory) (endianness : Endianness)
    (memory : Memory) (address : Address) :
    (width : AccessWidth) → AccessValue width → Memory
  | .byte, value => storage.writeByte memory address value
  | .half, value =>
      match endianness with
      | .little =>
          let memory := storage.writeByte memory address
            (value.extractLsb' 0 8)
          storage.writeByte memory (byteAddress address 1) (value.extractLsb' 8 8)
      | .big =>
          let memory := storage.writeByte memory address
            (value.extractLsb' 8 8)
          storage.writeByte memory (byteAddress address 1) (value.extractLsb' 0 8)
  | .word, value =>
      match endianness with
      | .little =>
          let memory := storage.writeByte memory address
            (value.extractLsb' 0 8)
          let memory := storage.writeByte memory (byteAddress address 1)
            (value.extractLsb' 8 8)
          let memory := storage.writeByte memory (byteAddress address 2)
            (value.extractLsb' 16 8)
          storage.writeByte memory (byteAddress address 3) (value.extractLsb' 24 8)
      | .big =>
          let memory := storage.writeByte memory address
            (value.extractLsb' 24 8)
          let memory := storage.writeByte memory (byteAddress address 1)
            (value.extractLsb' 16 8)
          let memory := storage.writeByte memory (byteAddress address 2)
            (value.extractLsb' 8 8)
          storage.writeByte memory (byteAddress address 3) (value.extractLsb' 0 8)

/-- Reading an access immediately after writing the same access returns the
written value, for either byte order and including misaligned addresses. -/
theorem readValue_writeValue_same
    (storage : ByteStorage Memory) (endianness : Endianness)
    (memory : Memory) (address : Address)
    (width : AccessWidth) (value : AccessValue width) :
    readValue storage endianness
      (writeValue storage endianness memory address width value)
      address width = value := by
  cases width <;> cases endianness
  case byte.little | byte.big => simp [readValue, writeValue]
  case half.little | half.big =>
    simp [readValue, writeValue, byteAddress]
    exact BitVec.extractLsb'_append_extractLsb'
  case word.little | word.big =>
    simp [readValue, writeValue, byteAddress]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
    exact BitVec.extractLsb'_append_extractLsb'

/-- A multibyte write leaves every byte outside its addressed byte offsets
unchanged. The offsets are interpreted modulo the 32-bit address space. -/
theorem readByte_writeValue_outside
    (storage : ByteStorage Memory) (endianness : Endianness)
    (memory : Memory) (address readAddress : Address)
    (width : AccessWidth) (value : AccessValue width)
    (outside : ∀ offset : Nat, offset < width.bytes →
      readAddress ≠ byteAddress address offset) :
    storage.readByte
      (writeValue storage endianness memory address width value)
      readAddress = storage.readByte memory readAddress := by
  cases width <;> cases endianness
  case byte.little | byte.big =>
    have h0 : readAddress ≠ address := by
      simpa using outside 0 (by decide)
    exact storage.read_write_other memory address readAddress value h0
  case half.little | half.big =>
    have h0 : readAddress ≠ address := by
      simpa using outside 0 (by decide)
    have h1 : readAddress ≠ byteAddress address 1 := by
      simpa using outside 1 (by decide)
    simp only [writeValue]
    rw [storage.read_write_other _ (byteAddress address 1) readAddress _ h1]
    rw [storage.read_write_other _ address readAddress _ h0]
  case word.little | word.big =>
    have h0 : readAddress ≠ address := by
      simpa using outside 0 (by decide)
    have h1 : readAddress ≠ byteAddress address 1 := by
      simpa using outside 1 (by decide)
    have h2 : readAddress ≠ byteAddress address 2 := by
      simpa using outside 2 (by decide)
    have h3 : readAddress ≠ byteAddress address 3 := by
      simpa using outside 3 (by decide)
    simp only [writeValue]
    rw [storage.read_write_other _ (byteAddress address 3) readAddress _ h3]
    rw [storage.read_write_other _ (byteAddress address 2) readAddress _ h2]
    rw [storage.read_write_other _ (byteAddress address 1) readAddress _ h1]
    rw [storage.read_write_other _ address readAddress _ h0]

/-- A total sequential-memory profile. Every 32-bit address denotes a byte, and
misaligned data accesses are assembled from those bytes rather than faulting.
The selected endianness gives the byte-address-to-value mapping. Multibyte
accesses crossing `0xffffffff` use `byteAddress` and therefore wrap to zero. -/
structure Semantics (Memory : Type) where
  storage : ByteStorage Memory
  endianness : Endianness

namespace Semantics

/-- Interpret one architectural request while holding exclusive access to the
abstract memory state. This is a single-request state interpretation, not an
evaluator loop or an RVWMO execution. -/
def interpret (semantics : Semantics Memory) (memory : Memory) :
    (request : Request) → request.Response × Memory
  | .memory (.fetch address _) =>
      (.success (readInstruction semantics.storage memory address), memory)
  | .memory (.load address width) =>
      (.success
        (readValue semantics.storage semantics.endianness memory address width),
        memory)
  | .memory (.store address width value) =>
      (.success (),
        writeValue semantics.storage semantics.endianness
          memory address width value)
  | .fence _ => ((), memory)

/-- The generic EEI relation induced by the sequential interpretation. -/
def environment (semantics : Semantics Memory) : ExecutionEnvironment Memory :=
  { responds := fun before request response after =>
      semantics.interpret before request = (response, after) }

@[simp] theorem responds_iff
    (semantics : Semantics Memory) (before : Memory)
    (request : Request) (response : request.Response) (after : Memory) :
    semantics.environment.responds before request response after ↔
      semantics.interpret before request = (response, after) :=
  Iff.rfl

/-- Fetch is a four-byte read and leaves memory state unchanged. -/
theorem responds_fetch
    (semantics : Semantics Memory) (memory : Memory)
    (address : Address) (aligned : address.toNat % 4 = 0) :
    semantics.environment.responds memory
      (.memory (.fetch address aligned))
      (.success (readInstruction semantics.storage memory address))
      memory := by
  rfl

/-- Selecting little- or big-endian data accesses does not change instruction
fetch. Both profiles assemble the same instruction word from the same four
bytes in RISC-V's fixed instruction-parcel order. -/
theorem responds_fetch_independent_of_data_endianness
    (storage : ByteStorage Memory) (memory : Memory)
    (address : Address) (aligned : address.toNat % 4 = 0) :
    let little : Semantics Memory :=
      { storage := storage, endianness := .little }
    let big : Semantics Memory :=
      { storage := storage, endianness := .big }
    little.environment.responds memory
        (.memory (.fetch address aligned))
        (.success (readInstruction storage memory address)) memory ∧
      big.environment.responds memory
        (.memory (.fetch address aligned))
        (.success (readInstruction storage memory address)) memory := by
  constructor <;> rfl

/-- Every load succeeds in this total profile, including a misaligned load. -/
theorem responds_load
    (semantics : Semantics Memory) (memory : Memory)
    (address : Address) (width : AccessWidth) :
    semantics.environment.responds memory
      (.memory (.load address width))
      (.success
        (readValue semantics.storage semantics.endianness memory address width))
      memory := by
  rfl

/-- Every store succeeds and produces exactly the ordered byte updates. -/
theorem responds_store
    (semantics : Semantics Memory) (memory : Memory)
    (address : Address) (width : AccessWidth) (value : AccessValue width) :
    semantics.environment.responds memory
      (.memory (.store address width value)) (.success ())
      (writeValue semantics.storage semantics.endianness
        memory address width value) := by
  rfl

/-- FENCE is acknowledged without changing byte values. Its architectural
effect remains recorded by `Interaction.Runs`. -/
theorem responds_fence
    (semantics : Semantics Memory) (memory : Memory) (fence : Fence) :
    semantics.environment.responds memory (.fence fence) () memory := by
  rfl

/-- Interpreting a fence preserves memory and still records the fence effect
in the generic interaction trace. -/
theorem fence_runs
    (semantics : Semantics Memory) (memory : Memory)
    (fence : Fence) (result : InstructionResult) :
    Interaction.Runs semantics.environment
      (.request (.fence fence) (fun _ => .done result))
      memory [.fence fence] result memory := by
  exact Interaction.Runs.request memory memory memory (.fence fence) ()
    (fun _ => .done result) [] result
    (responds_fence semantics memory fence)
    (Interaction.Runs.done memory result)

/-- The response and successor memory state are unique for each request. -/
theorem responds_deterministic
    (semantics : Semantics Memory) (before : Memory) (request : Request)
    (firstResponse secondResponse : request.Response)
    (firstAfter secondAfter : Memory)
    (first : semantics.environment.responds before request
      firstResponse firstAfter)
    (second : semantics.environment.responds before request
      secondResponse secondAfter) :
    firstResponse = secondResponse ∧ firstAfter = secondAfter := by
  have equalPairs : (firstResponse, firstAfter) =
      (secondResponse, secondAfter) := first.symm.trans second
  exact ⟨congrArg Prod.fst equalPairs, congrArg Prod.snd equalPairs⟩

/-- A store followed by a load of the same address and width returns the
stored value. This makes request-order threading explicit. -/
theorem store_then_load_same
    (semantics : Semantics Memory) (memory : Memory)
    (address : Address) (width : AccessWidth) (value : AccessValue width) :
    let afterStore := writeValue semantics.storage semantics.endianness
      memory address width value
    semantics.environment.responds memory
        (.memory (.store address width value)) (.success ()) afterStore ∧
      semantics.environment.responds afterStore
        (.memory (.load address width)) (.success value) afterStore := by
  dsimp
  constructor
  · exact responds_store semantics memory address width value
  · simpa [readValue_writeValue_same] using
      responds_load semantics
        (writeValue semantics.storage semantics.endianness
          memory address width value)
        address width

/-- Two stores are interpreted by threading the first successor state into
the second request, with no opportunity for another agent to intervene. -/
theorem stores_in_request_order
    (semantics : Semantics Memory) (memory : Memory)
    (firstAddress secondAddress : Address)
    (firstWidth secondWidth : AccessWidth)
    (firstValue : AccessValue firstWidth)
    (secondValue : AccessValue secondWidth) :
    let afterFirst := writeValue semantics.storage semantics.endianness
      memory firstAddress firstWidth firstValue
    let afterSecond := writeValue semantics.storage semantics.endianness
      afterFirst secondAddress secondWidth secondValue
    semantics.environment.responds memory
        (.memory (.store firstAddress firstWidth firstValue))
        (.success ()) afterFirst ∧
      semantics.environment.responds afterFirst
        (.memory (.store secondAddress secondWidth secondValue))
        (.success ()) afterSecond := by
  dsimp
  exact ⟨responds_store _ _ _ _ _, responds_store _ _ _ _ _⟩

end Semantics

end SequentialMemory

end RV32I
