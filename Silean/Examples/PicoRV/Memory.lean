import Silean.Foundation.BitVector
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Memory

open Silean

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

inductive Input
  | resetn | trap
  | mem_do_prefetch | mem_do_rinst | mem_do_rdata | mem_do_wdata
  | next_pc | reg_op1 | reg_op2 | mem_wordsize
  | mem_ready | mem_rdata
deriving Enumeration

inductive Output
  | mem_valid | mem_instr | mem_addr | mem_wdata | mem_wstrb
  | mem_la_read | mem_la_write | mem_la_addr | mem_la_wdata | mem_la_wstrb
  | mem_done | mem_rdata_word | mem_rdata_latched
  | mem_rdata_q
deriving Enumeration

inductive State
  | mem_state | mem_valid | mem_instr | mem_addr | mem_wdata | mem_wstrb
  | mem_rdata_q
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .next_pc | .reg_op1 | .reg_op2 | .mem_rdata => .vector 32 .bit
    | .mem_wordsize => .vector 2 .bit
    | _ => .bit

def outputType : Output → SignalType
  | .mem_addr | .mem_wdata | .mem_la_addr | .mem_la_wdata
  | .mem_rdata_word | .mem_rdata_latched | .mem_rdata_q => .vector 32 .bit
  | .mem_wstrb | .mem_la_wstrb => .vector 4 .bit
  | _ => .bit

@[reducible] def outputMap : SignalMap := EnumeratedMap.of Output outputType

def stateType : State → SignalType
  | .mem_state => .vector 2 .bit
  | .mem_addr | .mem_wdata | .mem_rdata_q => .vector 32 .bit
  | .mem_wstrb => .vector 4 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of State stateType
@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

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

def aligned (word : Word) : Word := wordOfNat (BitVector.toNat 32 word / 4 * 4)

def lowByte (word : Word) : Nat := BitVector.toNat 32 word % 256
def lowHalf (word : Word) : Nat := BitVector.toNat 32 word % 65536

def formattedWriteDataFrom (wordsize : TwoBits) (regOp2 : Word) : Word :=
  match BitVector.toNat 2 wordsize with
  | 1 => wordOfNat (lowHalf regOp2 * 65537)
  | 2 => wordOfNat (lowByte regOp2 * 0x01010101)
  | _ => regOp2

def formattedWriteData (inputs : Inputs) : Word :=
  formattedWriteDataFrom inputs.mem_wordsize inputs.reg_op2

def formattedWriteMaskFrom (wordsize : TwoBits) (regOp1 : Word) : ByteMask :=
  match BitVector.toNat 2 wordsize with
  | 1 => if regOp1 1 then maskOfNat 0xc else maskOfNat 0x3
  | 2 => maskOfNat (2 ^ (BitVector.toNat 32 regOp1 % 4))
  | _ => maskOfNat 0xf

def formattedWriteMask (inputs : Inputs) : ByteMask :=
  formattedWriteMaskFrom inputs.mem_wordsize inputs.reg_op1

def formattedReadDataFrom (wordsize : TwoBits) (regOp1 memRdata : Word) : Word :=
  let value := BitVector.toNat 32 memRdata
  match BitVector.toNat 2 wordsize with
  | 1 => wordOfNat ((value / (if regOp1 1 then 65536 else 1)) % 65536)
  | 2 => wordOfNat ((value / 2 ^ (8 * (BitVector.toNat 32 regOp1 % 4))) % 256)
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

def normalNextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  let laRead := memLaRead inputs current
  let laWrite := memLaWrite inputs current
  let xfer := memXfer inputs current
  let updated := if laRead || laWrite then
      let updated := stateMap.set updated .mem_addr (memLaAddr inputs)
      stateMap.set updated .mem_wstrb
        (if laWrite then formattedWriteMask inputs else maskOfNat 0)
    else updated
  let updated := if laWrite then
      stateMap.set updated .mem_wdata (formattedWriteData inputs)
    else updated
  match stateNumber current with
  | 0 =>
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
  | 1 =>
      if xfer then
        let updated := stateMap.set updated .mem_valid false
        stateMap.set updated .mem_state
          (stateOfNat (if inputs.mem_do_rinst || inputs.mem_do_rdata then 0 else 3))
      else updated
  | 2 =>
      if xfer then
        let updated := stateMap.set updated .mem_valid false
        stateMap.set updated .mem_state (stateOfNat 0)
      else updated
  | _ =>
      if inputs.mem_do_rinst then stateMap.set updated .mem_state (stateOfNat 0)
      else updated

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let updated := responseCaptured inputs state
  if !inputs.resetn || inputs.trap then
    let updated := if !inputs.resetn then
        stateMap.set updated .mem_state (stateOfNat 0)
      else updated
    if !inputs.resetn || inputs.mem_ready then stateMap.set updated .mem_valid false
    else updated
  else normalNextState inputs state updated

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
    simp [nextState, resetn, notTrap, normalNextState, requestState, xfer,
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
    simp [nextState, resetn, notTrap, normalNextState, stateNumber, requestBits,
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
    nextState, notTrap, normalNextState, phase, stateNumber, laRead, laWrite,
    responseCaptured, readBits]

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
    normalNextState, phase, stateNumber, laRead, laWrite, responseCaptured,
    prefetchedBits]

inductive Rule
  | registered
  | memLaRead | memLaWrite | memLaAddr | memLaWdata | memLaWstrb
  | memDone | memRdataWord | memRdataLatched | memRdataQ
deriving Enumeration

def registeredRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .nil,
      outputTypes := .ofList [
        .bit, .bit, .vector 32 .bit, .vector 32 .bit, .vector 4 .bit] } where
  readsInputs := .nil
  writesOutputs := ((((outputMap.select .mem_wstrb).prepend
    .mem_wdata).prepend .mem_addr).prepend .mem_instr).prepend .mem_valid
  target := fun _ state =>
    (state .mem_valid, (state .mem_instr, (state .mem_addr, (state .mem_wdata,
      (state .mem_wstrb, ())))))

def memLaReadRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.bit, .bit, .bit, .bit],
      outputTypes := .cons .bit .nil } where
  readsInputs := (((inputMap.select .mem_do_rdata).prepend .mem_do_rinst).prepend
    .mem_do_prefetch).prepend .resetn
  writesOutputs := outputMap.select .mem_la_read
  target
    | (resetn, (prefetch, (rinst, (rdata, ())))), state =>
      (memLaReadFrom resetn prefetch rinst rdata state, ())

def memLaWriteRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.bit, .bit], outputTypes := .cons .bit .nil } where
  readsInputs := (inputMap.select .mem_do_wdata).prepend .resetn
  writesOutputs := outputMap.select .mem_la_write
  target
    | (resetn, (wdata, ())), state =>
      (memLaWriteFrom resetn wdata state, ())

def memLaAddrRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.bit, .bit, .vector 32 .bit, .vector 32 .bit],
      outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := (((inputMap.select .reg_op1).prepend .next_pc).prepend
    .mem_do_rinst).prepend .mem_do_prefetch
  writesOutputs := outputMap.select .mem_la_addr
  target
    | (prefetch, (rinst, (nextPc, (regOp1, ())))), _ =>
      (memLaAddrFrom prefetch rinst nextPc regOp1, ())

def memLaWdataRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.vector 2 .bit, .vector 32 .bit],
      outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := (inputMap.select .reg_op2).prepend .mem_wordsize
  writesOutputs := outputMap.select .mem_la_wdata
  target
    | (wordsize, (regOp2, ())), _ =>
      (formattedWriteDataFrom wordsize regOp2, ())

def memLaWstrbRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.vector 2 .bit, .vector 32 .bit],
      outputTypes := .cons (.vector 4 .bit) .nil } where
  readsInputs := (inputMap.select .reg_op1).prepend .mem_wordsize
  writesOutputs := outputMap.select .mem_la_wstrb
  target
    | (wordsize, (regOp1, ())), _ =>
      (formattedWriteMaskFrom wordsize regOp1, ())

def memDoneRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.bit, .bit, .bit, .bit, .bit],
      outputTypes := .cons .bit .nil } where
  readsInputs := ((((inputMap.select .mem_ready).prepend .mem_do_wdata).prepend
    .mem_do_rdata).prepend .mem_do_rinst).prepend .resetn
  writesOutputs := outputMap.select .mem_done
  target
    | (resetn, (rinst, (rdata, (wdata, (ready, ()))))), state =>
      (memDoneFrom resetn rinst rdata wdata ready state, ())

def memRdataWordRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [
        .vector 2 .bit, .vector 32 .bit, .vector 32 .bit],
      outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := ((inputMap.select .mem_rdata).prepend .reg_op1).prepend .mem_wordsize
  writesOutputs := outputMap.select .mem_rdata_word
  target
    | (wordsize, (regOp1, (memRdata, ()))), _ =>
      (formattedReadDataFrom wordsize regOp1 memRdata, ())

def memRdataLatchedRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .ofList [.bit, .vector 32 .bit],
      outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := (inputMap.select .mem_rdata).prepend .mem_ready
  writesOutputs := outputMap.select .mem_rdata_latched
  target
    | (ready, (memRdata, ())), state =>
      (memRdataLatchedFrom ready memRdata state, ())

def memRdataQRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .nil,
      outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := .nil
  writesOutputs := outputMap.select .mem_rdata_q
  target := fun _ state => (state .mem_rdata_q, ())

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  inputTypes := .ofList inputMap.types
  readsInputs := inputMap.allSelection
  target := fun selected state =>
    nextState (inputsOfValues (inputMap.unpack selected)) state

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .registered => ⟨_, registeredRule⟩
    | .memLaRead => ⟨_, memLaReadRule⟩
    | .memLaWrite => ⟨_, memLaWriteRule⟩
    | .memLaAddr => ⟨_, memLaAddrRule⟩
    | .memLaWdata => ⟨_, memLaWdataRule⟩
    | .memLaWstrb => ⟨_, memLaWstrbRule⟩
    | .memDone => ⟨_, memDoneRule⟩
    | .memRdataWord => ⟨_, memRdataWordRule⟩
    | .memRdataLatched => ⟨_, memRdataLatchedRule⟩
    | .memRdataQ => ⟨_, memRdataQRule⟩
  stateRule := stateRule
  outputCoverage := by rfl

end Silean.Examples.PicoRV.Memory
