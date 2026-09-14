import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Authoring.SignalSchemaDeclaration
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Memory

open Silean
open Silean.Authoring

attribute [local simp] SignalMap.set_other

/-! Exact cycle contract for PicoRV32's single-outstanding memory interface in
the selected configuration (`COMPRESSED_ISA = 0`, `LATCHED_MEM_RDATA = 0`).

The contract keeps the source's registered external request and response
capture state. Compressed-instruction buffering registers are absent because
every use is disabled by the fixed configuration. The `mem_do_*` commands and
`mem_wordsize` remain inputs owned by the control child, matching the source
block that assigns them. -/

abbrev Word := Fin 32 → Bool
abbrev ByteMask := Fin 4 → Bool
abbrev TwoBits := Fin 2 → Bool

/-! The contract and structural implementation share named aggregates for the
seven source-owned registers and the complete combinational input boundary. -/

signal_schema MemoryState where
  mem_state : SignalSchema.vector 2 SignalSchema.bit,
  mem_valid : SignalSchema.bit,
  mem_instr : SignalSchema.bit,
  mem_addr : SignalSchema.vector 32 SignalSchema.bit,
  mem_wdata : SignalSchema.vector 32 SignalSchema.bit,
  mem_wstrb : SignalSchema.vector 4 SignalSchema.bit,
  mem_rdata_q : SignalSchema.vector 32 SignalSchema.bit

abbrev State := MemoryState.Field

@[reducible] def stateMap : SignalMap := MemoryState.signalMap

@[reducible] def stateType : SignalType := stateMap.tupleType

signal_schema MemoryInputs where
  resetn : SignalSchema.bit,
  trap : SignalSchema.bit,
  mem_do_prefetch : SignalSchema.bit,
  mem_do_rinst : SignalSchema.bit,
  mem_do_rdata : SignalSchema.bit,
  mem_do_wdata : SignalSchema.bit,
  next_pc : SignalSchema.vector 32 SignalSchema.bit,
  reg_op1 : SignalSchema.vector 32 SignalSchema.bit,
  reg_op2 : SignalSchema.vector 32 SignalSchema.bit,
  mem_wordsize : SignalSchema.vector 2 SignalSchema.bit,
  mem_ready : SignalSchema.bit,
  mem_rdata : SignalSchema.vector 32 SignalSchema.bit

@[reducible] def inputsType : SignalType := MemoryInputs.signalMap.tupleType

module_ports ports where
  input resetn : .bit,
  input trap : .bit,
  input mem_do_prefetch : .bit,
  input mem_do_rinst : .bit,
  input mem_do_rdata : .bit,
  input mem_do_wdata : .bit,
  input next_pc : .vector 32 .bit,
  input reg_op1 : .vector 32 .bit,
  input reg_op2 : .vector 32 .bit,
  input mem_wordsize : .vector 2 .bit,
  input mem_ready : .bit,
  input mem_rdata : .vector 32 .bit,
  output mem_valid : .bit,
  output mem_instr : .bit,
  output mem_addr : .vector 32 .bit,
  output mem_wdata : .vector 32 .bit,
  output mem_wstrb : .vector 4 .bit,
  output mem_la_read : .bit,
  output mem_la_write : .bit,
  output mem_la_addr : .vector 32 .bit,
  output mem_la_wdata : .vector 32 .bit,
  output mem_la_wstrb : .vector 4 .bit,
  output mem_done : .bit,
  output mem_rdata_word : .vector 32 .bit,
  output mem_rdata_latched : .vector 32 .bit,
  output mem_rdata_q : .vector 32 .bit

structure Inputs where
  resetn : Bool
  trap : Bool
  mem_do_prefetch : Bool
  mem_do_rinst : Bool
  mem_do_rdata : Bool
  mem_do_wdata : Bool
  next_pc : Word
  reg_op1 : Word
  reg_op2 : Word
  mem_wordsize : TwoBits
  mem_ready : Bool
  mem_rdata : Word

def Inputs.toValues (inputs : Inputs) : MemoryInputs.signalMap.Values
  | .resetn => inputs.resetn
  | .trap => inputs.trap
  | .mem_do_prefetch => inputs.mem_do_prefetch
  | .mem_do_rinst => inputs.mem_do_rinst
  | .mem_do_rdata => inputs.mem_do_rdata
  | .mem_do_wdata => inputs.mem_do_wdata
  | .next_pc => inputs.next_pc
  | .reg_op1 => inputs.reg_op1
  | .reg_op2 => inputs.reg_op2
  | .mem_wordsize => inputs.mem_wordsize
  | .mem_ready => inputs.mem_ready
  | .mem_rdata => inputs.mem_rdata

def Inputs.pack (inputs : Inputs) : inputsType.Denote :=
  MemoryInputs.signalMap.pack inputs.toValues

def Inputs.unpack (value : inputsType.Denote) : Inputs :=
  let fields := MemoryInputs.signalMap.unpack value
  { resetn := fields .resetn
    trap := fields .trap
    mem_do_prefetch := fields .mem_do_prefetch
    mem_do_rinst := fields .mem_do_rinst
    mem_do_rdata := fields .mem_do_rdata
    mem_do_wdata := fields .mem_do_wdata
    next_pc := fields .next_pc
    reg_op1 := fields .reg_op1
    reg_op2 := fields .reg_op2
    mem_wordsize := fields .mem_wordsize
    mem_ready := fields .mem_ready
    mem_rdata := fields .mem_rdata }

@[simp] theorem Inputs.unpack_pack (inputs : Inputs) :
    Inputs.unpack inputs.pack = inputs := by
  cases inputs
  simp [Inputs.unpack, Inputs.pack, Inputs.toValues]

@[simp] theorem Inputs.pack_unpack (value : inputsType.Denote) :
    (Inputs.unpack value).pack = value := by
  change (Inputs.unpack value).pack = value
  calc
    (Inputs.unpack value).pack =
        MemoryInputs.signalMap.pack (MemoryInputs.signalMap.unpack value) := by
      apply congrArg MemoryInputs.signalMap.pack
      funext field
      cases field <;> simp [Inputs.unpack, Inputs.toValues]
    _ = value := MemoryInputs.signalMap.pack_unpack value

def inputsOfValues (values : inputMap.Values) : Inputs where
  resetn := values .resetn
  trap := values .trap
  mem_do_prefetch := values .mem_do_prefetch
  mem_do_rinst := values .mem_do_rinst
  mem_do_rdata := values .mem_do_rdata
  mem_do_wdata := values .mem_do_wdata
  next_pc := values .next_pc
  reg_op1 := values .reg_op1
  reg_op2 := values .reg_op2
  mem_wordsize := values .mem_wordsize
  mem_ready := values .mem_ready
  mem_rdata := values .mem_rdata

def inputValues (inputs : Inputs) : inputMap.Values
  | .resetn => inputs.resetn
  | .trap => inputs.trap
  | .mem_do_prefetch => inputs.mem_do_prefetch
  | .mem_do_rinst => inputs.mem_do_rinst
  | .mem_do_rdata => inputs.mem_do_rdata
  | .mem_do_wdata => inputs.mem_do_wdata
  | .next_pc => inputs.next_pc
  | .reg_op1 => inputs.reg_op1
  | .reg_op2 => inputs.reg_op2
  | .mem_wordsize => inputs.mem_wordsize
  | .mem_ready => inputs.mem_ready
  | .mem_rdata => inputs.mem_rdata

@[simp] theorem inputsOfValues_inputValues (inputs : Inputs) :
    inputsOfValues (inputValues inputs) = inputs := by
  cases inputs
  rfl

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val
def maskOfNat (value : Nat) : ByteMask := fun index => value.testBit index.val
def stateOfNat (value : Nat) : TwoBits := fun index => value.testBit index.val

@[simp] theorem stateOfNat_zero : BitVector.toNat 2 (stateOfNat 0) = 0 := by decide
@[simp] theorem stateOfNat_one : BitVector.toNat 2 (stateOfNat 1) = 1 := by decide
@[simp] theorem stateOfNat_two : BitVector.toNat 2 (stateOfNat 2) = 2 := by decide
@[simp] theorem stateOfNat_three : BitVector.toNat 2 (stateOfNat 3) = 3 := by decide

def wordSize (inputs : Inputs) : Nat := BitVector.toNat 2 inputs.mem_wordsize
def stateNumber (state : stateMap.Values) : Nat := BitVector.toNat 2 (state .mem_state)

def aligned (word : Word) : Word := fun index =>
  if index.val < 2 then false else word index

def lowAddressBits (word : Word) : TwoBits := fun index =>
  word ⟨index.val, by omega⟩

def lowByte (word : Word) : Nat := BitVector.toNat 32 word % 256
def lowHalf (word : Word) : Nat := BitVector.toNat 32 word % 65536

def formattedWriteDataFrom (wordsize : TwoBits) (regOp2 : Word) : Word :=
  match BitVector.toNat 2 wordsize with
  | 1 => fun index => regOp2 ⟨index.val % 16, by omega⟩
  | 2 => fun index => regOp2 ⟨index.val % 8, by omega⟩
  | _ => regOp2

def formattedWriteData (inputs : Inputs) : Word :=
  formattedWriteDataFrom inputs.mem_wordsize inputs.reg_op2

def formattedWriteMaskFrom (wordsize : TwoBits) (regOp1 : Word) : ByteMask :=
  match BitVector.toNat 2 wordsize with
  | 1 => if regOp1 1 then maskOfNat 0xc else maskOfNat 0x3
  | 2 => fun index => decide
      (index.val = BitVector.toNat 2 (lowAddressBits regOp1))
  | _ => maskOfNat 0xf

def formattedWriteMask (inputs : Inputs) : ByteMask :=
  formattedWriteMaskFrom inputs.mem_wordsize inputs.reg_op1

def formattedReadDataFrom (wordsize : TwoBits) (regOp1 memRdata : Word) : Word :=
  match BitVector.toNat 2 wordsize with
  | 1 => fun index =>
      if low : index.val < 16 then
        memRdata ⟨index.val + if regOp1 1 then 16 else 0, by
          cases high : regOp1 1 <;> simp <;> omega⟩
      else false
  | 2 =>
      let byte := BitVector.toNat 2 (lowAddressBits regOp1)
      fun index =>
        if low : index.val < 8 then
          memRdata ⟨index.val + 8 * byte, by
            have bound := BitVector.toNat_lt_cardinality 2 (lowAddressBits regOp1)
            simp [BitVector.cardinality] at bound
            omega⟩
        else false
  | _ => memRdata

def formattedReadData (inputs : Inputs) : Word :=
  formattedReadDataFrom inputs.mem_wordsize inputs.reg_op1 inputs.mem_rdata

@[simp] def memXferFrom (memReady : Bool) (state : stateMap.Values) : Bool :=
  state .mem_valid && memReady

def memXfer (inputs : Inputs) (state : stateMap.Values) : Bool :=
  memXferFrom inputs.mem_ready state

def memBusyFrom (prefetch rinst rdata wdata : Bool) : Bool :=
  prefetch || rinst || rdata || wdata

def memBusy (inputs : Inputs) : Bool :=
  memBusyFrom inputs.mem_do_prefetch inputs.mem_do_rinst
    inputs.mem_do_rdata inputs.mem_do_wdata

def activeCompletionCommand (inputs : Inputs) : Bool :=
  inputs.mem_do_rinst || inputs.mem_do_rdata || inputs.mem_do_wdata

@[simp] def memDoneFrom (resetn rinst rdata wdata memReady : Bool)
    (state : stateMap.Values) : Bool :=
  resetn &&
    ((memXferFrom memReady state && decide (stateNumber state ≠ 0) &&
        (rinst || rdata || wdata)) ||
      (decide (stateNumber state = 3) && rinst))

def memDone (inputs : Inputs) (state : stateMap.Values) : Bool :=
  memDoneFrom inputs.resetn inputs.mem_do_rinst inputs.mem_do_rdata
    inputs.mem_do_wdata inputs.mem_ready state

@[simp] def memLaReadFrom (resetn prefetch rinst rdata : Bool)
    (state : stateMap.Values) : Bool :=
  resetn && decide (stateNumber state = 0) && (rinst || prefetch || rdata)

def memLaRead (inputs : Inputs) (state : stateMap.Values) : Bool :=
  memLaReadFrom inputs.resetn inputs.mem_do_prefetch inputs.mem_do_rinst
    inputs.mem_do_rdata state

@[simp] def memLaWriteFrom (resetn wdata : Bool) (state : stateMap.Values) : Bool :=
  resetn && decide (stateNumber state = 0) && wdata

def memLaWrite (inputs : Inputs) (state : stateMap.Values) : Bool :=
  memLaWriteFrom inputs.resetn inputs.mem_do_wdata state

def memLaAddrFrom (prefetch rinst : Bool) (nextPc regOp1 : Word) : Word :=
  if prefetch || rinst then aligned nextPc else aligned regOp1

def memLaAddr (inputs : Inputs) : Word :=
  memLaAddrFrom inputs.mem_do_prefetch inputs.mem_do_rinst
    inputs.next_pc inputs.reg_op1

def memRdataLatchedFrom (memReady : Bool) (memRdata : Word)
    (state : stateMap.Values) : Word :=
  if memXferFrom memReady state then memRdata else state .mem_rdata_q

def memRdataLatched (inputs : Inputs) (state : stateMap.Values) : Word :=
  memRdataLatchedFrom inputs.mem_ready inputs.mem_rdata state

def outputValues (inputs : Inputs) (state : stateMap.Values) : outputMap.Values
  | .mem_valid => state .mem_valid
  | .mem_instr => state .mem_instr
  | .mem_addr => state .mem_addr
  | .mem_wdata => state .mem_wdata
  | .mem_wstrb => state .mem_wstrb
  | .mem_la_read => memLaRead inputs state
  | .mem_la_write => memLaWrite inputs state
  | .mem_la_addr => memLaAddr inputs
  | .mem_la_wdata => formattedWriteData inputs
  | .mem_la_wstrb => formattedWriteMask inputs
  | .mem_done => memDone inputs state
  | .mem_rdata_word => formattedReadData inputs
  | .mem_rdata_latched => memRdataLatched inputs state
  | .mem_rdata_q => state .mem_rdata_q

def responseCaptured (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  if !memXfer inputs state then state else
  stateMap.set state .mem_rdata_q inputs.mem_rdata

def lookaheadCaptured (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  let laRead := memLaRead inputs current
  let laWrite := memLaWrite inputs current
  let updated := if laRead || laWrite then
      let updated := stateMap.set updated .mem_addr (memLaAddr inputs)
      stateMap.set updated .mem_wstrb
        (if laWrite then formattedWriteMask inputs else maskOfNat 0)
    else updated
  let updated := if laWrite then
      stateMap.set updated .mem_wdata (formattedWriteData inputs)
    else updated
  updated

def idleNextState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values :=
  let updated := if inputs.mem_do_prefetch || inputs.mem_do_rinst || inputs.mem_do_rdata then
      let updated := stateMap.set updated .mem_valid true
      let updated := stateMap.set updated .mem_instr
        (inputs.mem_do_prefetch || inputs.mem_do_rinst)
      let updated := stateMap.set updated .mem_wstrb (maskOfNat 0)
      stateMap.set updated .mem_state (stateOfNat 1)
    else updated
  if inputs.mem_do_wdata then
    let updated := stateMap.set updated .mem_valid true
    let updated := stateMap.set updated .mem_instr false
    stateMap.set updated .mem_state (stateOfNat 2)
  else updated

def readNextState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  if memXfer inputs current then
    let updated := stateMap.set updated .mem_valid false
    stateMap.set updated .mem_state
      (stateOfNat (if inputs.mem_do_rinst || inputs.mem_do_rdata then 0 else 3))
  else updated

def writeNextState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  if memXfer inputs current then
    let updated := stateMap.set updated .mem_valid false
    stateMap.set updated .mem_state (stateOfNat 0)
  else updated

def prefetchedNextState (inputs : Inputs) (updated : stateMap.Values) :
    stateMap.Values :=
  if inputs.mem_do_rinst then stateMap.set updated .mem_state (stateOfNat 0)
  else updated

def normalNextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  let updated := lookaheadCaptured inputs current updated
  match stateNumber current with
  | 0 => idleNextState inputs updated
  | 1 => readNextState inputs current updated
  | 2 => writeNextState inputs current updated
  | _ => prefetchedNextState inputs updated

def resetTrapApplied (inputs : Inputs) (captured normal : stateMap.Values) :
    stateMap.Values :=
  if !inputs.resetn || inputs.trap then
    let updated := if !inputs.resetn then
        stateMap.set captured .mem_state (stateOfNat 0)
      else captured
    if !inputs.resetn || inputs.mem_ready then stateMap.set updated .mem_valid false
    else updated
  else normal

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let captured := responseCaptured inputs state
  resetTrapApplied inputs captured (normalNextState inputs state captured)

/-! Data reads and writes are exclusive with every other command. PicoRV32
does intentionally assert `mem_do_prefetch` and `mem_do_rinst` together when a
prefetched request is promoted to the current instruction, so those two
instruction-side commands are the sole permitted overlap. -/
def CommandsWellFormed (inputs : Inputs) : Prop :=
  (inputs.mem_do_rdata = true →
    inputs.mem_do_prefetch = false ∧ inputs.mem_do_rinst = false ∧
      inputs.mem_do_wdata = false) ∧
  (inputs.mem_do_wdata = true →
    inputs.mem_do_prefetch = false ∧ inputs.mem_do_rinst = false ∧
      inputs.mem_do_rdata = false)

def InputsWellFormed (inputs : Inputs) : Prop :=
  CommandsWellFormed inputs ∧ wordSize inputs ≤ 2

structure Request where
  instruction : Bool
  address : Word
  writeData : Word
  writeMask : ByteMask

def request? (state : stateMap.Values) : Option Request :=
  let valid : Bool := state .mem_valid
  if valid then some {
    instruction := state .mem_instr
    address := state .mem_addr
    writeData := state .mem_wdata
    writeMask := state .mem_wstrb
  } else none

/-! `Phase`, `request?`, and the laws below are the natural protocol view of
the exact register transition. There can be at most one external request
because it is represented by one optional value. A request remains unchanged
under backpressure. Ordinary instruction/data reads and writes complete on
their one external transfer; a pure prefetch instead waits in `prefetched`
until control promotes it with `mem_do_rinst`.

As in `picorv32.v`, command compatibility and deassertion after `mem_done` are
caller obligations. The control contract must establish them; without
that obligation, held level commands intentionally start another request after
the state machine returns to idle. -/

inductive Phase
  | idle
  | readRequest
  | writeRequest
  | prefetched
deriving DecidableEq

def phase (state : stateMap.Values) : Phase :=
  match stateNumber state with
  | 0 => .idle
  | 1 => .readRequest
  | 2 => .writeRequest
  | _ => .prefetched

theorem request_stable_while_stalled (inputs : Inputs) (state : stateMap.Values)
    (resetn : inputs.resetn = true) (notTrap : inputs.trap = false)
    (active : state .mem_valid = true) (stalled : inputs.mem_ready = false)
    (requestState : stateNumber state = 1 ∨ stateNumber state = 2) :
    request? (nextState inputs state) = request? state := by
  have xfer : memXfer inputs state = false := by simp [memXfer, active, stalled]
  have laRead : memLaRead inputs state = false := by
    rcases requestState with requestState | requestState <;>
      simp [memLaRead, resetn, requestState]
  have laWrite : memLaWrite inputs state = false := by
    rcases requestState with requestState | requestState <;>
      simp [memLaWrite, resetn, requestState]
  rcases requestState with requestState | requestState <;>
    simp [nextState, resetn, notTrap, resetTrapApplied, normalNextState,
      lookaheadCaptured, readNextState, writeNextState, requestState, xfer,
      laRead, laWrite, responseCaptured, active, request?]

theorem no_completion_while_stalled (inputs : Inputs) (state : stateMap.Values)
    (stalled : inputs.mem_ready = false) (notPrefetched : stateNumber state ≠ 3) :
    memDone inputs state = false := by
  simp [memDone, stalled]
  omega

theorem transfer_completes_active_command (inputs : Inputs) (state : stateMap.Values)
    (resetn : inputs.resetn = true) (nonidle : stateNumber state ≠ 0)
    (transfer : memXfer inputs state = true)
    (active : activeCompletionCommand inputs = true) :
    memDone inputs state = true := by
  simp [memXfer, activeCompletionCommand] at transfer active
  simp [memDone, resetn, nonidle, transfer, active]

theorem completed_read_or_write_returns_idle (inputs : Inputs)
    (state : stateMap.Values) (resetn : inputs.resetn = true)
    (notTrap : inputs.trap = false) (transfer : memXfer inputs state = true)
    (requestAndCommand :
      (stateNumber state = 1 ∧ (inputs.mem_do_rinst || inputs.mem_do_rdata) = true) ∨
      (stateNumber state = 2 ∧ inputs.mem_do_wdata = true)) :
    phase (nextState inputs state) = .idle ∧
      (nextState inputs state) .mem_valid = false := by
  rcases requestAndCommand with ⟨requestState, command⟩ | ⟨requestState, command⟩
  all_goals
    have requestBits : BitVector.toNat 2 (state .mem_state) = _ := requestState
    have laRead : memLaRead inputs state = false := by
      simp [memLaRead, resetn, requestState]
    have laWrite : memLaWrite inputs state = false := by
      simp [memLaWrite, resetn, requestState]
    simp [nextState, resetn, notTrap, resetTrapApplied, normalNextState,
      lookaheadCaptured, readNextState, writeNextState, stateNumber, requestBits,
      transfer, laRead, laWrite, responseCaptured, phase, command]

theorem prefetch_transfer_waits_for_instruction_command (inputs : Inputs)
    (state : stateMap.Values) (resetn : inputs.resetn = true)
    (notTrap : inputs.trap = false) (readState : stateNumber state = 1)
    (transfer : memXfer inputs state = true)
    (_prefetch : inputs.mem_do_prefetch = true)
    (notInstruction : inputs.mem_do_rinst = false)
    (notData : inputs.mem_do_rdata = false)
    (notWrite : inputs.mem_do_wdata = false) :
    memDone inputs state = false ∧ phase (nextState inputs state) = .prefetched := by
  have readBits : BitVector.toNat 2 (state .mem_state) = 1 := readState
  have notIdle : stateNumber state ≠ 0 := by omega
  have laRead : memLaRead inputs state = false := by
    simp [memLaRead, resetn, notIdle]
  have laWrite : memLaWrite inputs state = false := by
    simp [memLaWrite, resetn, notIdle]
  simp [memDone, resetn, transfer, notInstruction, notData, notWrite,
    nextState, notTrap, resetTrapApplied, normalNextState, lookaheadCaptured,
    readNextState, phase, stateNumber, laRead, laWrite, responseCaptured,
    readBits]

theorem prefetched_instruction_completes_without_transfer (inputs : Inputs)
    (state : stateMap.Values) (resetn : inputs.resetn = true)
    (notTrap : inputs.trap = false) (prefetched : stateNumber state = 3)
    (instruction : inputs.mem_do_rinst = true)
    (noTransfer : memXfer inputs state = false) :
    memDone inputs state = true ∧ phase (nextState inputs state) = .idle := by
  have prefetchedBits : BitVector.toNat 2 (state .mem_state) = 3 := prefetched
  have notIdle : stateNumber state ≠ 0 := by omega
  have laRead : memLaRead inputs state = false := by
    simp [memLaRead, resetn, notIdle]
  have laWrite : memLaWrite inputs state = false := by
    simp [memLaWrite, resetn, notIdle]
  simp [memDone, resetn, instruction, noTransfer, nextState, notTrap,
    resetTrapApplied, normalNextState, lookaheadCaptured, prefetchedNextState,
    phase, stateNumber, laRead, laWrite, responseCaptured, prefetchedBits]

namespace RegisteredRule
inductive Output | mem_valid | mem_instr | mem_addr | mem_wdata | mem_wstrb
deriving Enumeration
end RegisteredRule

namespace MemLaReadRule
inductive Input | resetn | mem_do_prefetch | mem_do_rinst | mem_do_rdata
deriving Enumeration
inductive Output | mem_la_read deriving Enumeration
end MemLaReadRule

namespace MemLaWriteRule
inductive Input | resetn | mem_do_wdata deriving Enumeration
inductive Output | mem_la_write deriving Enumeration
end MemLaWriteRule

namespace MemLaAddrRule
inductive Input | mem_do_prefetch | mem_do_rinst | next_pc | reg_op1
deriving Enumeration
inductive Output | mem_la_addr deriving Enumeration
end MemLaAddrRule

namespace MemLaWdataRule
inductive Input | mem_wordsize | reg_op2 deriving Enumeration
inductive Output | mem_la_wdata deriving Enumeration
end MemLaWdataRule

namespace MemLaWstrbRule
inductive Input | mem_wordsize | reg_op1 deriving Enumeration
inductive Output | mem_la_wstrb deriving Enumeration
end MemLaWstrbRule

namespace MemDoneRule
inductive Input | resetn | mem_do_rinst | mem_do_rdata | mem_do_wdata | mem_ready
deriving Enumeration
inductive Output | mem_done deriving Enumeration
end MemDoneRule

namespace MemRdataWordRule
inductive Input | mem_wordsize | reg_op1 | mem_rdata deriving Enumeration
inductive Output | mem_rdata_word deriving Enumeration
end MemRdataWordRule

namespace MemRdataLatchedRule
inductive Input | mem_ready | mem_rdata deriving Enumeration
inductive Output | mem_rdata_latched deriving Enumeration
end MemRdataLatchedRule

namespace MemRdataQRule
inductive Output | mem_rdata_q deriving Enumeration
end MemRdataQRule

@[reducible] private def registeredOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap RegisteredRule.Output fun
    | .mem_valid => .mem_valid
    | .mem_instr => .mem_instr
    | .mem_addr => .mem_addr
    | .mem_wdata => .mem_wdata
    | .mem_wstrb => .mem_wstrb

@[reducible] private def memLaReadInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemLaReadRule.Input fun
    | .resetn => .resetn
    | .mem_do_prefetch => .mem_do_prefetch
    | .mem_do_rinst => .mem_do_rinst
    | .mem_do_rdata => .mem_do_rdata

@[reducible] private def memLaReadOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemLaReadRule.Output fun
    | .mem_la_read => .mem_la_read

@[reducible] private def memLaWriteInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemLaWriteRule.Input fun
    | .resetn => .resetn
    | .mem_do_wdata => .mem_do_wdata

@[reducible] private def memLaWriteOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemLaWriteRule.Output fun
    | .mem_la_write => .mem_la_write

@[reducible] private def memLaAddrInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemLaAddrRule.Input fun
    | .mem_do_prefetch => .mem_do_prefetch
    | .mem_do_rinst => .mem_do_rinst
    | .next_pc => .next_pc
    | .reg_op1 => .reg_op1

@[reducible] private def memLaAddrOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemLaAddrRule.Output fun
    | .mem_la_addr => .mem_la_addr

@[reducible] private def memLaWdataInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemLaWdataRule.Input fun
    | .mem_wordsize => .mem_wordsize
    | .reg_op2 => .reg_op2

@[reducible] private def memLaWdataOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemLaWdataRule.Output fun
    | .mem_la_wdata => .mem_la_wdata

@[reducible] private def memLaWstrbInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemLaWstrbRule.Input fun
    | .mem_wordsize => .mem_wordsize
    | .reg_op1 => .reg_op1

@[reducible] private def memLaWstrbOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemLaWstrbRule.Output fun
    | .mem_la_wstrb => .mem_la_wstrb

@[reducible] private def memDoneInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemDoneRule.Input fun
    | .resetn => .resetn
    | .mem_do_rinst => .mem_do_rinst
    | .mem_do_rdata => .mem_do_rdata
    | .mem_do_wdata => .mem_do_wdata
    | .mem_ready => .mem_ready

@[reducible] private def memDoneOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemDoneRule.Output fun
    | .mem_done => .mem_done

@[reducible] private def memRdataWordInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemRdataWordRule.Input fun
    | .mem_wordsize => .mem_wordsize
    | .reg_op1 => .reg_op1
    | .mem_rdata => .mem_rdata

@[reducible] private def memRdataWordOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemRdataWordRule.Output fun
    | .mem_rdata_word => .mem_rdata_word

@[reducible] private def memRdataLatchedInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap MemRdataLatchedRule.Input fun
    | .mem_ready => .mem_ready
    | .mem_rdata => .mem_rdata

@[reducible] private def memRdataLatchedOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemRdataLatchedRule.Output fun
    | .mem_rdata_latched => .mem_rdata_latched

@[reducible] private def memRdataQOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap MemRdataQRule.Output fun
    | .mem_rdata_q => .mem_rdata_q

def registeredRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := registeredOutputs
  target _ state := fun
    | .mem_valid => state .mem_valid
    | .mem_instr => state .mem_instr
    | .mem_addr => state .mem_addr
    | .mem_wdata => state .mem_wdata
    | .mem_wstrb => state .mem_wstrb

def memLaReadRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memLaReadInputs
  writesOutputs := memLaReadOutputs
  target inputs state := fun
    | .mem_la_read =>
      memLaReadFrom (inputs .resetn) (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata) state

def memLaWriteRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memLaWriteInputs
  writesOutputs := memLaWriteOutputs
  target inputs state := fun
    | .mem_la_write =>
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) state

def memLaAddrRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memLaAddrInputs
  writesOutputs := memLaAddrOutputs
  target inputs _ := fun
    | .mem_la_addr =>
      memLaAddrFrom (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .next_pc) (inputs .reg_op1)

def memLaWdataRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memLaWdataInputs
  writesOutputs := memLaWdataOutputs
  target inputs _ := fun
    | .mem_la_wdata =>
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2)

def memLaWstrbRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memLaWstrbInputs
  writesOutputs := memLaWstrbOutputs
  target inputs _ := fun
    | .mem_la_wstrb =>
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1)

def memDoneRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memDoneInputs
  writesOutputs := memDoneOutputs
  target inputs state := fun
    | .mem_done =>
      memDoneFrom (inputs .resetn) (inputs .mem_do_rinst)
        (inputs .mem_do_rdata) (inputs .mem_do_wdata) (inputs .mem_ready) state

def memRdataWordRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memRdataWordInputs
  writesOutputs := memRdataWordOutputs
  target inputs _ := fun
    | .mem_rdata_word =>
      formattedReadDataFrom (inputs .mem_wordsize) (inputs .reg_op1)
        (inputs .mem_rdata)

def memRdataLatchedRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := memRdataLatchedInputs
  writesOutputs := memRdataLatchedOutputs
  target inputs state := fun
    | .mem_rdata_latched =>
      memRdataLatchedFrom (inputs .mem_ready) (inputs .mem_rdata) state

def memRdataQRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := memRdataQOutputs
  target _ state := fun | .mem_rdata_q => state .mem_rdata_q

@[simp] theorem registeredRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    registeredRule.Holds inputs state outputs ↔
      outputs .mem_valid = state .mem_valid ∧
      outputs .mem_instr = state .mem_instr ∧
      outputs .mem_addr = state .mem_addr ∧
      outputs .mem_wdata = state .mem_wdata ∧
      outputs .mem_wstrb = state .mem_wstrb := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, registeredRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every
    exact ⟨every .mem_valid, every .mem_instr, every .mem_addr,
      every .mem_wdata, every .mem_wstrb⟩
  · rintro ⟨valid, instr, addr, wdata, wstrb⟩ output
    cases output
    · exact valid
    · exact instr
    · exact addr
    · exact wdata
    · exact wstrb

@[simp] theorem memLaReadRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memLaReadRule.Holds inputs state outputs ↔
      outputs .mem_la_read = memLaReadFrom (inputs .resetn)
        (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .mem_do_rdata) state := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memLaReadRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_la_read
  · intro equal output; cases output; exact equal

@[simp] theorem memLaWriteRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memLaWriteRule.Holds inputs state outputs ↔
      outputs .mem_la_write = memLaWriteFrom (inputs .resetn)
        (inputs .mem_do_wdata) state := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memLaWriteRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_la_write
  · intro equal output; cases output; exact equal

@[simp] theorem memLaAddrRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memLaAddrRule.Holds inputs state outputs ↔
      outputs .mem_la_addr = memLaAddrFrom (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .next_pc) (inputs .reg_op1) := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memLaAddrRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_la_addr
  · intro equal output; cases output; exact equal

@[simp] theorem memLaWdataRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memLaWdataRule.Holds inputs state outputs ↔
      outputs .mem_la_wdata = formattedWriteDataFrom
        (inputs .mem_wordsize) (inputs .reg_op2) := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memLaWdataRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_la_wdata
  · intro equal output; cases output; exact equal

@[simp] theorem memLaWstrbRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memLaWstrbRule.Holds inputs state outputs ↔
      outputs .mem_la_wstrb = formattedWriteMaskFrom
        (inputs .mem_wordsize) (inputs .reg_op1) := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memLaWstrbRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_la_wstrb
  · intro equal output; cases output; exact equal

@[simp] theorem memDoneRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memDoneRule.Holds inputs state outputs ↔
      outputs .mem_done = memDoneFrom (inputs .resetn)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata)
        (inputs .mem_do_wdata) (inputs .mem_ready) state := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memDoneRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_done
  · intro equal output; cases output; exact equal

@[simp] theorem memRdataWordRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memRdataWordRule.Holds inputs state outputs ↔
      outputs .mem_rdata_word = formattedReadDataFrom
        (inputs .mem_wordsize) (inputs .reg_op1) (inputs .mem_rdata) := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memRdataWordRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_rdata_word
  · intro equal output; cases output; exact equal

@[simp] theorem memRdataLatchedRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memRdataLatchedRule.Holds inputs state outputs ↔
      outputs .mem_rdata_latched = memRdataLatchedFrom
        (inputs .mem_ready) (inputs .mem_rdata) state := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memRdataLatchedRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_rdata_latched
  · intro equal output; cases output; exact equal

@[simp] theorem memRdataQRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    memRdataQRule.Holds inputs state outputs ↔
      outputs .mem_rdata_q = state .mem_rdata_q := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, memRdataQRule,
    SignalGroup.fromLabels_matches_iff]
  constructor
  · intro every; exact every .mem_rdata_q
  · intro equal output; cases output; exact equal

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target := fun inputs state => nextState (inputsOfValues inputs) state

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule registered := registeredRule
  output_rule memLaRead := memLaReadRule
  output_rule memLaWrite := memLaWriteRule
  output_rule memLaAddr := memLaAddrRule
  output_rule memLaWdata := memLaWdataRule
  output_rule memLaWstrb := memLaWstrbRule
  output_rule memDone := memDoneRule
  output_rule memRdataWord := memRdataWordRule
  output_rule memRdataLatched := memRdataLatchedRule
  output_rule memRdataQ := memRdataQRule
  state_rule := stateRule

end Silean.Examples.PicoRV.Memory
