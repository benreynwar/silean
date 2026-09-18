import RV32I
import LeanRV32D.InstsEnd

/-!
Bridge-only vocabulary for one RV32I data-memory access and the generated
Sail model's physical-memory interface. The public model deliberately does not
import this module or expose generated request types.
-/

namespace RV32I.SailBridge

open Sail
open Sail.ConcurrencyInterfaceV1
open LeanRV32D
open LeanRV32D.Functions

/-- The selected address profile for the unprivileged RV32I bridge is Sail's
`Bare` translation case: a clean 32-bit effective address becomes the same
numeric physical address, zero-extended to the generated model's 34-bit
physical-address width. Page-table translation is outside this profile. -/
def sailPhysicalAddress (address : RV32I.Address) : LeanRV32D.physaddrbits :=
  LeanRV32D.zero_extend (m := 34) address

/-- The generated virtual-address wrapper used before Bare translation. -/
def sailVirtualAddress (address : RV32I.Address) : LeanRV32D.virtaddr :=
  .Virtaddr address

@[simp] theorem sailVirtualAddress_bits (address : RV32I.Address) :
    LeanRV32D.Functions.bits_of_virtaddr (sailVirtualAddress address) = address :=
  rfl

/-- This is the address expression in the `Bare` branch of generated
`translateAddr`; it establishes that the bridge profile is not a truncating or
relocating address convention. -/
theorem generated_bare_physical_address (address : RV32I.Address) :
    LeanRV32D.physaddr.Physaddr
        (LeanRV32D.zero_extend (m := 34)
          (LeanRV32D.Functions.bits_of_virtaddr (sailVirtualAddress address))) =
      .Physaddr (sailPhysicalAddress address) :=
  rfl

/-- Audited generated configuration facts relevant to this layer. -/
theorem generated_xlen_is_32 : LeanRV32D.Functions.xlen = 32 := rfl

theorem generated_physical_address_width_is_34 :
    LeanRV32D.Functions.physaddr_bits = 34 := rfl

/-- The reviewed platform permits ordinary misaligned load/store accesses to
continue to its physical-access machinery; it does not force an alignment
exception at the virtual-memory entry point. -/
theorem generated_plain_misaligned_policy :
    LeanRV32D.Functions.plat_misaligned_access.load_store = none := rfl

/-- The exact generated concurrency-interface type used by a plain data read
of a clean architectural width. -/
abbrev SailReadRequest (width : RV32I.AccessWidth) :=
  Mem_read_request width.bytes 64 LeanRV32D.physaddrbits Unit
    LeanRV32D.RISCV_strong_access

/-- The exact generated concurrency-interface type used by a plain data write
of a clean architectural width. -/
abbrev SailWriteRequest (width : RV32I.AccessWidth) :=
  Mem_write_request width.bytes 64 LeanRV32D.physaddrbits Unit
    LeanRV32D.RISCV_strong_access

/-- Plain, non-exclusive, normally ordered access kind emitted by generated
RV32I `LW` and `SW` after translation and physical access checks. -/
def sailPlainAccessKind : Access_kind LeanRV32D.RISCV_strong_access :=
  .AK_explicit { variety := .AV_plain, strength := .AS_normal }

/-- Convert the clean width-indexed payload convention (`bytes * 8`) to the
generated request convention (`8 * bytes`). -/
def toSailAccessValue (width : RV32I.AccessWidth)
    (value : RV32I.AccessValue width) : BitVec (8 * width.bytes) :=
  cast (by cases width <;> rfl) value

/-- Convert a generated memory result back to the clean width-indexed payload
convention. -/
def ofSailAccessValue (width : RV32I.AccessWidth)
    (value : BitVec (8 * width.bytes)) : RV32I.AccessValue width :=
  cast (by cases width <;> rfl) value

@[simp] theorem ofSailAccessValue_toSailAccessValue
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    ofSailAccessValue width (toSailAccessValue width value) = value := by
  cases width <;> rfl

@[simp] theorem toSailAccessValue_ofSailAccessValue
    (width : RV32I.AccessWidth) (value : BitVec (8 * width.bytes)) :
    toSailAccessValue width (ofSailAccessValue width value) = value := by
  cases width <;> rfl

/-- The literal read request constructed by generated `read_ram Read_plain`
under the selected Bare address profile. `va` is absent because translation
has already happened before the concurrency interface is called. -/
def sailReadRequest (address : RV32I.Address) (width : RV32I.AccessWidth) :
    SailReadRequest width :=
  { access_kind := sailPlainAccessKind
    va := none
    pa := sailPhysicalAddress address
    translation := ()
    size := width.bytes
    tag := false }

/-- The literal write request constructed by generated `write_ram Write_plain`
under the selected Bare address profile. -/
def sailWriteRequest (address : RV32I.Address) (width : RV32I.AccessWidth)
    (value : RV32I.AccessValue width) : SailWriteRequest width :=
  { access_kind := sailPlainAccessKind
    va := none
    pa := sailPhysicalAddress address
    translation := ()
    size := width.bytes
    value := some (toSailAccessValue width value)
    tag := none }

/-- The generated sequential backend action for the exact plain read request.
This is factored here only so the following theorem can check the request
record against generated `read_ram`; it is not a public memory semantics. -/
def sailReadRamAction (address : RV32I.Address) (width : RV32I.AccessWidth) :
    LeanRV32D.SailM (BitVec (8 * width.bytes) × Unit) := do
  match (← @LeanRV32D.ConcurrencyInterfaceV1.sail_mem_read
      width.bytes 64 34 Unit LeanRV32D.RISCV_strong_access
      LeanRV32D.instArch_leanRV32D (sailReadRequest address width)) with
  | .Ok (value, _) => pure (value, ())
  | .Err () => throw Error.Exit

/-- The generated sequential backend action for the exact plain write
request. The returned Boolean is backend success, not an architectural fault
classification. -/
def sailWriteRamAction (address : RV32I.Address) (width : RV32I.AccessWidth)
    (value : RV32I.AccessValue width) : LeanRV32D.SailM Bool := do
  match (← @LeanRV32D.ConcurrencyInterfaceV1.sail_mem_write
      width.bytes 64 34 Unit LeanRV32D.RISCV_strong_access
      LeanRV32D.instArch_leanRV32D (sailWriteRequest address width value)) with
  | .Ok _ => pure true
  | .Err () => pure false

/-- The literal request above is exactly the one generated `read_ram
Read_plain` sends to the concurrency interface in this profile. -/
theorem generated_read_ram_plain (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    LeanRV32D.Functions.read_ram .Read_plain
        (.Physaddr (sailPhysicalAddress address)) width.bytes false =
      sailReadRamAction address width := by
  cases width <;>
    simp [LeanRV32D.Functions.read_ram, sailReadRamAction,
      sailReadRequest, sailPlainAccessKind, LeanRV32D.Functions.default_meta,
      Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_read]

/-- The literal request above is exactly the one generated `write_ram
Write_plain` sends to the concurrency interface in this profile. -/
theorem generated_write_ram_plain (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    LeanRV32D.Functions.write_ram .Write_plain
        (.Physaddr (sailPhysicalAddress address)) width.bytes
        (toSailAccessValue width value) () =
      sailWriteRamAction address width value := by
  cases width <;> rfl

/-- A dependent wrapper allowing clean load and store requests to be related
to the differently typed generated read and write requests. -/
inductive SailDataRequest where
  | read (width : RV32I.AccessWidth) (request : SailReadRequest width)
  | write (width : RV32I.AccessWidth) (request : SailWriteRequest width)

/-- Exact request correspondence for one clean architectural data access in
the selected Bare profile. Fetch is intentionally absent. -/
inductive DataRequestCorresponds : RV32I.MemoryRequest → SailDataRequest → Prop
  | load (address : RV32I.Address) (width : RV32I.AccessWidth) :
      DataRequestCorresponds (.load address width)
        (.read width (sailReadRequest address width))
  | store (address : RV32I.Address) (width : RV32I.AccessWidth)
      (value : RV32I.AccessValue width) :
      DataRequestCorresponds (.store address width value)
        (.write width (sailWriteRequest address width value))

/-- A clean data request selects one canonical generated request in this
profile. -/
theorem dataRequestCorresponds_unique {clean : RV32I.MemoryRequest}
    {first second : SailDataRequest}
    (firstCorresponds : DataRequestCorresponds clean first)
    (secondCorresponds : DataRequestCorresponds clean second) :
    first = second := by
  cases firstCorresponds <;> cases secondCorresponds <;> rfl

/-- Generated result immediately above the concurrency interface, after
physical access checks. Its error retains a generated physical fault address
and exception kind. -/
abbrev SailLoadResult (width : RV32I.AccessWidth) :=
  Result (BitVec (8 * width.bytes)) (LeanRV32D.physaddr × LeanRV32D.ExceptionType)

/-- Generated store result immediately above the concurrency interface. A
successful plain store has result `true`; `false` is reserved for a failed
conditional/backend write and is not a clean successful store response. -/
abbrev SailStoreResult :=
  Result Bool (LeanRV32D.physaddr × LeanRV32D.ExceptionType)

/-- Response correspondence for a clean load. The clean EEI does not expose
Sail's physical fault address, so that extra generated datum is existentially
forgotten. Bare translation excludes page faults; only the two RV32I data
access failures represented by the clean response type correspond. -/
inductive LoadResponseCorresponds {address : RV32I.Address}
    {width : RV32I.AccessWidth} :
    RV32I.DataResponse width address (RV32I.AccessValue width) →
      SailLoadResult width → Prop
  | success (value : RV32I.AccessValue width) :
      LoadResponseCorresponds (.success value) (.Ok (toSailAccessValue width value))
  | accessFault (faultAddress : LeanRV32D.physaddr) :
      LoadResponseCorresponds .accessFault
        (.Err (faultAddress, .E_Load_Access_Fault ()))
  | addressMisaligned (proof : ¬ width.Aligned address)
      (faultAddress : LeanRV32D.physaddr) :
      LoadResponseCorresponds (.addressMisaligned proof)
        (.Err (faultAddress, .E_Load_Addr_Align ()))

/-- Response correspondence for a clean store. Sail calls store faults
`SAMO` faults because stores and atomic memory operations share an exception
class in the generated model. -/
inductive StoreResponseCorresponds {address : RV32I.Address}
    {width : RV32I.AccessWidth} :
    RV32I.DataResponse width address Unit → SailStoreResult → Prop
  | success : StoreResponseCorresponds (.success ()) (.Ok true)
  | accessFault (faultAddress : LeanRV32D.physaddr) :
      StoreResponseCorresponds .accessFault
        (.Err (faultAddress, .E_SAMO_Access_Fault ()))
  | addressMisaligned (proof : ¬ width.Aligned address)
      (faultAddress : LeanRV32D.physaddr) :
      StoreResponseCorresponds (.addressMisaligned proof)
        (.Err (faultAddress, .E_SAMO_Addr_Align ()))

@[simp] theorem sailReadRequest_access_kind (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    (sailReadRequest address width).access_kind = sailPlainAccessKind := rfl

@[simp] theorem sailReadRequest_virtual_address (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    (sailReadRequest address width).va = none := rfl

@[simp] theorem sailReadRequest_physical_address (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    (sailReadRequest address width).pa = sailPhysicalAddress address := rfl

@[simp] theorem sailReadRequest_size (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    (sailReadRequest address width).size = width.bytes := rfl

@[simp] theorem sailReadRequest_tag (address : RV32I.Address)
    (width : RV32I.AccessWidth) :
    (sailReadRequest address width).tag = false := rfl

@[simp] theorem sailWriteRequest_access_kind (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).access_kind =
      sailPlainAccessKind := rfl

@[simp] theorem sailWriteRequest_virtual_address (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).va = none := rfl

@[simp] theorem sailWriteRequest_physical_address (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).pa = sailPhysicalAddress address := rfl

@[simp] theorem sailWriteRequest_size (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).size = width.bytes := rfl

@[simp] theorem sailWriteRequest_value (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).value =
      some (toSailAccessValue width value) := rfl

@[simp] theorem sailWriteRequest_tag (address : RV32I.Address)
    (width : RV32I.AccessWidth) (value : RV32I.AccessValue width) :
    (sailWriteRequest address width value).tag = none := rfl

theorem load_success_value {address : RV32I.Address}
    {width : RV32I.AccessWidth} {cleanValue : RV32I.AccessValue width}
    {sailValue : BitVec (8 * width.bytes)}
    (corresponds : LoadResponseCorresponds
      (address := address) (.success cleanValue) (.Ok sailValue)) :
    ofSailAccessValue width sailValue = cleanValue := by
  cases corresponds
  simp

theorem load_success_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} {cleanValue : RV32I.AccessValue width}
    {result : SailLoadResult width} :
    LoadResponseCorresponds (address := address) (.success cleanValue) result ↔
      result = .Ok (toSailAccessValue width cleanValue) := by
  constructor
  · intro corresponds
    cases corresponds
    rfl
  · rintro rfl
    exact .success cleanValue

theorem store_success_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} {result : SailStoreResult} :
    StoreResponseCorresponds (address := address) (width := width)
        (.success ()) result ↔ result = .Ok true := by
  constructor
  · intro corresponds
    cases corresponds
    rfl
  · rintro rfl
    exact .success

theorem load_accessFault_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} {result : SailLoadResult width} :
    LoadResponseCorresponds (address := address) (.accessFault) result ↔
      ∃ faultAddress, result =
        .Err (faultAddress, .E_Load_Access_Fault ()) := by
  constructor
  · intro corresponds
    cases corresponds with
    | accessFault faultAddress => exact ⟨faultAddress, rfl⟩
  · rintro ⟨faultAddress, rfl⟩
    exact .accessFault faultAddress

theorem store_accessFault_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} {result : SailStoreResult} :
    StoreResponseCorresponds (address := address) (width := width)
        (.accessFault) result ↔
      ∃ faultAddress, result =
        .Err (faultAddress, .E_SAMO_Access_Fault ()) := by
  constructor
  · intro corresponds
    cases corresponds with
    | accessFault faultAddress => exact ⟨faultAddress, rfl⟩
  · rintro ⟨faultAddress, rfl⟩
    exact .accessFault faultAddress

theorem load_addressMisaligned_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} (proof : ¬ width.Aligned address)
    {result : SailLoadResult width} :
    LoadResponseCorresponds (address := address)
        (.addressMisaligned proof) result ↔
      ∃ faultAddress, result =
        .Err (faultAddress, .E_Load_Addr_Align ()) := by
  constructor
  · intro corresponds
    cases corresponds with
    | addressMisaligned _ faultAddress => exact ⟨faultAddress, rfl⟩
  · rintro ⟨faultAddress, rfl⟩
    exact .addressMisaligned proof faultAddress

theorem store_addressMisaligned_iff {address : RV32I.Address}
    {width : RV32I.AccessWidth} (proof : ¬ width.Aligned address)
    {result : SailStoreResult} :
    StoreResponseCorresponds (address := address) (width := width)
        (.addressMisaligned proof) result ↔
      ∃ faultAddress, result =
        .Err (faultAddress, .E_SAMO_Addr_Align ()) := by
  constructor
  · intro corresponds
    cases corresponds with
    | addressMisaligned _ faultAddress => exact ⟨faultAddress, rfl⟩
  · rintro ⟨faultAddress, rfl⟩
    exact .addressMisaligned proof faultAddress

end RV32I.SailBridge
