namespace RV32I

abbrev Word := BitVec 32
abbrev Address := BitVec 32
abbrev Register := Fin 32

/-- Storage for `x1` through `x31`; architectural `x0` has no stored value. -/
abbrev WritableRegister := Fin 31

/-- Convert an architectural register number to its storage index, if writable. -/
def Register.writable? (register : Register) : Option WritableRegister :=
  if h : register.val = 0 then
    none
  else
    some ⟨register.val - 1, by omega⟩

/-- The hart-owned unprivileged architectural state. Memory and trap handling
belong to the execution environment. -/
structure State where
  pc : Address
  registers : Vector Word 31
  deriving DecidableEq, Repr

/-- Read an architectural register. `x0` always reads as zero. -/
def State.readRegister (state : State) (register : Register) : Word :=
  match register.writable? with
  | none => 0
  | some writable => state.registers[writable]

/-- Write an architectural register. Writes to `x0` have no effect. -/
def State.writeRegister (state : State) (register : Register) (value : Word) : State :=
  match register.writable? with
  | none => state
  | some writable =>
      { state with
        registers := state.registers.set writable value }

@[simp] theorem State.readRegister_zero (state : State) :
    state.readRegister 0 = 0 := by
  rfl

@[simp] theorem State.writeRegister_zero (state : State) (value : Word) :
    state.writeRegister 0 value = state := by
  rfl

/-- Width of one architectural data-memory access. -/
inductive AccessWidth where
  | byte
  | half
  | word
  deriving DecidableEq, Repr

def AccessWidth.bytes : AccessWidth → Nat
  | .byte => 1
  | .half => 2
  | .word => 4

/-- The exact payload transferred by an access of the given width. -/
abbrev AccessValue (width : AccessWidth) := BitVec (width.bytes * 8)

/-- Natural alignment for a data access. -/
def AccessWidth.Aligned (width : AccessWidth) (address : Address) : Prop :=
  address.toNat % width.bytes = 0

instance (width : AccessWidth) (address : Address) : Decidable (width.Aligned address) :=
  inferInstanceAs (Decidable (address.toNat % width.bytes = 0))

/-- A request made by the hart to its execution environment.

Instruction fetch is distinct from explicit data accesses. Store payloads are
width-indexed, so values outside the transferred byte lanes do not exist. A
data request denotes one architectural access at its 32-bit effective start
address. It does not prescribe component-byte addresses, address translation,
or whether an access spanning the top of the effective-address space succeeds;
those decisions belong to the EEI.
-/
inductive MemoryRequest where
  | fetch (address : Address) (aligned : address.toNat % 4 = 0)
  | load (address : Address) (width : AccessWidth)
  | store (address : Address) (width : AccessWidth) (value : AccessValue width)

/-- Result of an aligned instruction fetch. IALIGN=32 checking is performed
before a fetch request is issued. -/
inductive FetchResponse where
  | success (instruction : Word)
  | accessFault
  deriving DecidableEq, Repr

/-- Result of an explicit data access.

An access fault is possible at any address. An address-misaligned response
contains evidence that the request really was misaligned, so an EEI cannot
return that response for a naturally aligned access. A misaligned request may
also succeed or report an access fault, as required by the unprivileged ISA.
-/
inductive DataResponse (width : AccessWidth) (address : Address) (value : Type) where
  | success (result : value)
  | accessFault
  | addressMisaligned (misaligned : ¬ width.Aligned address)

def DataResponse.IsAddressMisaligned
    {width : AccessWidth} {address : Address} {value : Type} :
    DataResponse width address value → Prop
  | .addressMisaligned _ => True
  | _ => False

/-- The proof carried by `addressMisaligned` rules that response out for every
naturally aligned access. -/
theorem DataResponse.not_addressMisaligned_of_aligned
    {width : AccessWidth} {address : Address} {value : Type}
    (aligned : width.Aligned address) (response : DataResponse width address value) :
    ¬ response.IsAddressMisaligned := by
  cases response with
  | success | accessFault => simp [IsAddressMisaligned]
  | addressMisaligned misaligned => exact (misaligned aligned).elim

/-- The response type is determined by the request. -/
def MemoryRequest.Response : MemoryRequest → Type
  | .fetch _ _ => FetchResponse
  | .load address width => DataResponse width address (AccessValue width)
  | .store address width _ => DataResponse width address Unit

/-- One completed architectural memory access. A misaligned access may later
be related to multiple component memory operations by an RVWMO model. -/
structure MemoryAccess where
  request : MemoryRequest
  response : request.Response

/-- The four predecessor/successor classes named by an RV32I FENCE. -/
structure FenceSet where
  input : Bool
  output : Bool
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

/-- Decode the architectural `IORW` bit order used by the FENCE predecessor
and successor fields. -/
def FenceSet.ofBits (bits : BitVec 4) : FenceSet :=
  { input := bits.extractLsb' 3 1 == 1
    output := bits.extractLsb' 2 1 == 1
    read := bits.extractLsb' 1 1 == 1
    write := bits.extractLsb' 0 1 == 1 }

/-- The architectural ordering action of a decoded FENCE instruction.

`normal` also represents reserved FENCE configurations, which base
implementations must treat as if `fm=0000`; their predecessor and successor
fields retain their ordinary meaning while `rs1` and `rd` are ignored. `tso`
denotes only the exact FENCE.TSO encoding. FENCE.I is not RV32I.
-/
inductive Fence where
  | normal (predecessor successor : FenceSet)
  | tso
  deriving DecidableEq, Repr

/-- A request from the hart to its execution environment. Fences are ordering
actions, not memory accesses, and therefore form a separate case. -/
inductive Request where
  | memory (request : MemoryRequest)
  | fence (fence : Fence)

/-- A memory request receives its typed memory response. A fence cannot fault
and needs only acknowledgement that its ordering action has completed. -/
def Request.Response : Request → Type
  | .memory request => request.Response
  | .fence _ => Unit

/-- Architectural effects recorded in order while executing instructions. -/
inductive Effect where
  | memoryAccess (access : MemoryAccess)
  | fence (fence : Fence)

/-- Complete an EEI request into the architectural effect recorded by an
execution. Response values remain part of completed memory accesses. -/
def Request.effect : (request : Request) → request.Response → Effect
  | Request.memory request, response => .memoryAccess { request, response }
  | Request.fence f, () => Effect.fence f

/-- A resumable, executable interaction with an execution environment. -/
inductive Interaction (result : Type) where
  | done (result : result)
  | request (request : Request)
      (resume : request.Response → Interaction result)

/-- An unprivileged architectural exception together with the information
available at its point of origin. This is information delivered to the EEI;
it neither introduces privileged trap state nor prescribes trap entry.

Keeping the offending word or address here avoids throwing information away
before an EEI decides how to report or handle the exception. -/
inductive Exception where
  | illegalInstruction (instruction : Word)
  | environmentCall
  | breakpoint
  | instructionAddressMisaligned (target : Address)
  | instructionAccessFault (address : Address)
  | loadAddressMisaligned (address : Address)
  | loadAccessFault (address : Address)
  | storeAddressMisaligned (address : Address)
  | storeAccessFault (address : Address)
  deriving DecidableEq, Repr

/-- Architectural result of an attempted instruction. The EEI decides whether
and how a raised exception is handled. -/
inductive InstructionResult where
  | retired (nextState : State)
  | raised (state : State) (exception : Exception)
  deriving DecidableEq, Repr

/-- An EEI may be deterministic or relational. Its state can contain RAM,
devices, logs, or other platform-specific information. In particular, it may
change state even when it returns an access fault. -/
structure ExecutionEnvironment (environmentState : Type) where
  responds : environmentState → (request : Request) →
    request.Response → environmentState → Prop

/-- Relational execution of a resumable interaction against an EEI, recording
the ordered sequence of architectural effects. -/
inductive Interaction.Runs {result environmentState : Type}
    (environment : ExecutionEnvironment environmentState) :
    Interaction result → environmentState → List Effect →
      result → environmentState → Prop where
  | done (state : environmentState) (result : result) :
      Runs environment (.done result) state [] result state
  | request
      (before middle after : environmentState)
      (request : Request)
      (response : request.Response)
      (resume : request.Response → Interaction result)
      (effects : List Effect)
      (result : result)
      (responds : environment.responds before request response middle)
      (runs : Runs environment (resume response) middle effects result after) :
      Runs environment (.request request resume) before
        (request.effect response :: effects) result after

/-- A continuation has a unique next interaction once its response is fixed. -/
theorem Interaction.response_deterministic
    {result : Type} {request : Request}
    (resume : request.Response → Interaction result) (response : request.Response) :
    ∃ next, resume response = next ∧
      ∀ other, resume response = other → other = next := by
  refine ⟨resume response, rfl, ?_⟩
  intro other equal
  exact equal.symm

end RV32I
