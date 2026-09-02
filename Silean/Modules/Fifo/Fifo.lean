import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.EnabledResetCounter
import Silean.Interfaces.FifoPorts
import Silean.Modules.Fifo.FifoPointerControl
import Silean.Modules.RegisterBank
import Silean.Naming.FifoPortsNaming

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo
open Contracts.Cycle.Certification.Layer

/-- A FIFO with `2 ^ addressWidth` entries of `element`, built from a register
bank with read and write pointers.

The extra high bit in each pointer distinguishes a full buffer from an empty
one when their address bits are equal. Reset is synchronous; invalid storage
contents do not need to be cleared. -/

abbrev Pointer (addressWidth : Nat) :=
  EnabledResetCounter.Value (addressWidth + 1)

/-- Both counters start at the first entry, making the FIFO empty. -/
def zeroPointer (addressWidth : Nat) : Pointer addressWidth := fun _ => false

/-! ## Hardware structure -/

/-- The instances used to build the FIFO. -/
private inductive Instance
  /-- Tracks the entry currently presented at the output. -/
  | readCounter
  /-- Tracks the entry where the next accepted input will be stored. -/
  | writeCounter
  /-- Derives handshake decisions and storage addresses from the pointers. -/
  | control
  /-- Holds the FIFO's data entries. -/
  | storage
deriving Enumeration

@[reducible] private def instancePorts (element : SignalType)
    (addressWidth : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .readCounter | .writeCounter =>
        EnabledResetCounter.ports (addressWidth + 1)
    | .control => Fifo.PointerControl.ports addressWidth
    | .storage => RegisterBank.ports element addressWidth 1

@[reducible] private def context (element : SignalType)
    (addressWidth : Nat) : EndpointContext where
  ports := ports element
  instancePorts := instancePorts element addressWidth

/-- Connects the FIFO boundary and its instances. -/
private def wiring (element : SignalType) (addressWidth : Nat) :
    Wiring (context element addressWidth).ports
      (context element addressWidth).instancePorts :=
  let c := context element addressWidth
  { moduleOutput := fun
    -- Boundary outputs come from the control logic and selected storage entry.
    | .outputValid => c.instanceOutput .control .outputValid
    | .outputData => c.instanceOutput .storage (.readValue 0)
    | .inputReady => c.instanceOutput .control .inputReady
    instanceInput := fun
    -- The control logic advances and resets the read pointer.
    | .readCounter, .enable =>
        c.instanceOutput .control .readAdvance
    | .readCounter, .reset => c.moduleInput .reset
    -- The control logic advances and resets the write pointer.
    | .writeCounter, .enable =>
        c.instanceOutput .control .writeAdvance
    | .writeCounter, .reset => c.moduleInput .reset
    -- The control logic observes both pointers and the external handshake.
    | .control, .readPointer =>
        c.instanceOutput .readCounter .value
    | .control, .writePointer =>
        c.instanceOutput .writeCounter .value
    | .control, .inputValid => c.moduleInput .inputValid
    | .control, .outputReady => c.moduleInput .outputReady
    -- An accepted input writes its data at the current write pointer.
    | .storage, .writeEnable =>
        c.instanceOutput .control .writeAdvance
    | .storage, .writeAddress =>
        c.instanceOutput .control .writeAddress
    | .storage, .writeValue => c.moduleInput .inputData
    -- The current read pointer selects the value presented at the output.
    | .storage, .readAddress 0 =>
        c.instanceOutput .control .readAddress }

@[reducible] private def body (element : SignalType) (addressWidth : Nat) : ModuleBody :=
  ⟨context element addressWidth, wiring element addressWidth⟩

@[reducible] private def structuralChildren (element : SignalType)
    (addressWidth : Nat) :
    (name : (instancePorts element addressWidth).Name) →
      ModuleStructure ((instancePorts element addressWidth).ports name)
  | .readCounter | .writeCounter =>
      EnabledResetCounter.moduleStructure (addressWidth + 1) (zeroPointer addressWidth)
  | .control => Fifo.PointerControl.moduleStructure addressWidth
  | .storage => RegisterBank.moduleStructure element addressWidth 1

/-- The concrete FIFO hierarchy consumed by naming and FIRRTL generation. -/
def moduleStructure (element : SignalType) (addressWidth : Nat) :
    ModuleStructure (ports element) :=
  .composite (body element addressWidth) (structuralChildren element addressWidth)

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

/-- Rules describing the FIFO's combinational outputs. -/
inductive Rule
  /-- Produces `outputValid`, `outputData`, and `inputReady`. -/
  | observe
deriving Enumeration

def outputRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element) (stateMap element addressWidth)
      { inputTypes := .cons .bit (.cons .bit .nil)
        outputTypes := .cons .bit (.cons element (.cons .bit .nil)) } where
  readsInputs := ((inputMap element).select .outputReady).prepend .inputValid
  writesOutputs := (((outputMap element).select .inputReady).prepend
    .outputData).prepend .outputValid
  target
    | (_, (_outputReady, ())), state =>
        (outputValid (state .readPointer) (state .writePointer),
          (outputData addressWidth (state .readPointer) (state .entries),
            (inputReady (state .readPointer) (state .writePointer), ())))

def stateRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.CycleStateRule (ports element) (stateMap element addressWidth) where
  inputTypes := .cons .bit (.cons element (.cons .bit (.cons .bit .nil)))
  readsInputs := ((((inputMap element).select .reset).prepend .outputReady).prepend
    .inputData).prepend .inputValid
  target
    | (inputValid, (inputData, (outputReady, (reset, ())))), state => fun
        | .readPointer => nextReadPointer addressWidth reset outputReady
            (state .readPointer) (state .writePointer)
        | .writePointer => nextWritePointer addressWidth reset inputValid
            (state .readPointer) (state .writePointer)
        | .entries => nextEntries addressWidth inputValid inputData
            (state .readPointer) (state .writePointer) (state .entries)

@[reducible] def cycleContract (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element) where
  state := stateMap element addressWidth
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule element addressWidth⟩
  stateRule := stateRule element addressWidth
  outputCoverage := by rfl

/-! ## Contract-facing laws -/

@[simp] theorem outputRule_holds_iff (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element).outputs.Values) :
    (outputRule element addressWidth).Holds inputs state outputs ↔
      outputs .outputValid = outputValid (state .readPointer) (state .writePointer) ∧
      outputs .outputData = outputData addressWidth (state .readPointer) (state .entries) ∧
      outputs .inputReady = inputReady (state .readPointer) (state .writePointer) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

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

/-! ## Cycle certification

Everything below this point is proof construction. It connects the structure
shown at the beginning of the file to the exact cycle contract above; none of
it is consumed by FIRRTL generation. -/

@[reducible] private def childContracts (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (body element addressWidth)
  | .readCounter | .writeCounter =>
      EnabledResetCounter.cycleContract (addressWidth + 1) (zeroPointer addressWidth)
  | .control => Fifo.PointerControl.cycleContract addressWidth
  | .storage => RegisterBank.cycleContract element addressWidth 1

private abbrev readCounterRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth) (childContracts element addressWidth) :=
  ⟨.readCounter, EnabledResetCounter.Rule.observe⟩

private abbrev writeCounterRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth) (childContracts element addressWidth) :=
  ⟨.writeCounter, EnabledResetCounter.Rule.observe⟩

private abbrev controlRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth) (childContracts element addressWidth) :=
  ⟨.control, Fifo.PointerControl.Rule.apply⟩

private abbrev storageRule (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth) (childContracts element addressWidth) :=
  ⟨.storage, RegisterBank.Rule.read 0⟩

private def scheduleOrders (element : SignalType) (addressWidth : Nat) :
    ScheduleDerivation.RuleScheduleOrders (body element addressWidth)
      (childContracts element addressWidth) (cycleContract element addressWidth) where
  output := fun
    | .observe => [readCounterRule element addressWidth,
        writeCounterRule element addressWidth, controlRule element addressWidth,
        storageRule element addressWidth]
  state := [readCounterRule element addressWidth,
    writeCounterRule element addressWidth, controlRule element addressWidth]

private def derivedRuleSchedules (element : SignalType) (addressWidth : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (body element addressWidth)
      (childContracts element addressWidth) (cycleContract element addressWidth) := by
  derive_rule_schedules (scheduleOrders element addressWidth)

private abbrev ruleSchedules (element : SignalType) (addressWidth : Nat) :=
  (derivedRuleSchedules element addressWidth).schedules

private theorem coversChildren (element : SignalType) (addressWidth : Nat) :
    (ruleSchedules element addressWidth).CoversChildren :=
  (derivedRuleSchedules element addressWidth).coversChildren

section LayerCertification

variable (element : SignalType) (addressWidth : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body element addressWidth) (childContracts element addressWidth))

private def stateCorresponds
    (contractState : (stateMap element addressWidth).Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth) layerChildren).State) : Prop :=
  (layerChildren .readCounter).certification.stateCorresponds
      (fun | .stored => contractState .readPointer) (structuralState .readCounter) ∧
  (layerChildren .writeCounter).certification.stateCorresponds
      (fun | .stored => contractState .writePointer) (structuralState .writeCounter) ∧
  (layerChildren .storage).certification.stateCorresponds
      (fun | .entries => contractState .entries) (structuralState .storage)

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth) layerChildren).State) :
    ∃ contractState,
      stateCorresponds element addressWidth layerChildren contractState structuralState := by
  rcases (layerChildren .readCounter).certification.hasCorrespondingState
      (structuralState .readCounter) with ⟨readState, readCorresponds⟩
  rcases (layerChildren .writeCounter).certification.hasCorrespondingState
      (structuralState .writeCounter) with ⟨writeState, writeCorresponds⟩
  rcases (layerChildren .storage).certification.hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  let contractState : (stateMap element addressWidth).Values := fun
    | .readPointer => readState .stored
    | .writePointer => writeState .stored
    | .entries => storageState .entries
  exact ⟨contractState, readCorresponds, writeCorresponds, storageCorresponds⟩

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body element addressWidth) layerChildren)
      (cycleContract element addressWidth)
      (stateCorresponds element addressWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases corresponds with ⟨readCorresponds, writeCorresponds, storageCorresponds⟩
  have readMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .readCounter (fun | .stored => contractState .readPointer) readCorresponds
  have writeMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .writeCounter (fun | .stored => contractState .writePointer) writeCorresponds
  have storageMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .storage (fun | .entries => contractState .entries) storageCorresponds
  have controlMatches :=
    letI : Subsingleton (childContracts element addressWidth .control).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .control SignalMap.emptyValues
  rcases readMatches with ⟨readEvaluates, readNextCorresponds⟩
  rcases writeMatches with ⟨writeEvaluates, writeNextCorresponds⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases controlMatches with ⟨controlEvaluates, _⟩
  have readCurrent : (proposal.2 .readCounter).outputs .value =
      contractState .readPointer :=
    (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (readEvaluates.1 EnabledResetCounter.Rule.observe)
  have writeCurrent : (proposal.2 .writeCounter).outputs .value =
      contractState .writePointer :=
    (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (writeEvaluates.1 EnabledResetCounter.Rule.observe)
  have controlValues :=
    (Fifo.PointerControl.outputRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.apply)
  have controlInputRead : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .readPointer =
      (proposal.2 .readCounter).outputs .value := rfl
  have controlInputWrite : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .writePointer =
      (proposal.2 .writeCounter).outputs .value := rfl
  have controlInputValid : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .inputValid =
      inputs .inputValid := rfl
  have controlOutputReady : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .outputReady =
      inputs .outputReady := rfl
  have controlReadAddress : (proposal.2 .control).outputs .readAddress =
      Fifo.PointerControl.pointerAddress (contractState .readPointer) := by
    rw [controlValues.1]
    exact congrArg Fifo.PointerControl.pointerAddress readCurrent
  have controlWriteAddress : (proposal.2 .control).outputs .writeAddress =
      Fifo.PointerControl.pointerAddress (contractState .writePointer) := by
    rw [controlValues.2.1]
    exact congrArg Fifo.PointerControl.pointerAddress writeCurrent
  have controlReady : (proposal.2 .control).outputs .inputReady =
      inputReady (contractState .readPointer) (contractState .writePointer) := by
    rw [controlValues.2.2.1]
    simp only [inputReady]
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent]
  have controlValid : (proposal.2 .control).outputs .outputValid =
      outputValid (contractState .readPointer) (contractState .writePointer) := by
    rw [controlValues.2.2.2.1]
    simp only [outputValid]
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent]
  have controlReadAdvance : (proposal.2 .control).outputs .readAdvance =
      readAdvance (contractState .readPointer) (contractState .writePointer)
        (inputs .outputReady) := by
    rw [controlValues.2.2.2.2.1]
    simp only [readAdvance]
    rw [controlInputRead, controlInputWrite, controlOutputReady,
      readCurrent, writeCurrent]
  have controlWriteAdvance : (proposal.2 .control).outputs .writeAdvance =
      writeAdvance (contractState .readPointer) (contractState .writePointer)
        (inputs .inputValid) := by
    rw [controlValues.2.2.2.2.2]
    simp only [writeAdvance]
    rw [controlInputRead, controlInputWrite, controlInputValid,
      readCurrent, writeCurrent]
  have storageRead : (proposal.2 .storage).outputs (.readValue 0) =
      outputData addressWidth (contractState .readPointer)
        (contractState .entries) := by
    have held := (RegisterBank.readRule_holds_iff element addressWidth 1 0 _ _ _).mp
      (storageEvaluates.1 (RegisterBank.Rule.read 0))
    rw [held]
    unfold outputData
    rw [show (ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .storage) (.readAddress 0) =
        (proposal.2 .control).outputs .readAddress by rfl,
      controlReadAddress]
  let nextContractState : (stateMap element addressWidth).Values :=
    (stateRule element addressWidth).apply inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      exact ⟨(satisfies.1 .outputValid).trans controlValid,
        (satisfies.1 .outputData).trans storageRead,
        (satisfies.1 .inputReady).trans controlReady⟩
    · rfl
  · refine ⟨?_, ?_, ?_⟩
    · change (layerChildren .readCounter).certification.stateCorresponds
        (fun | .stored => nextContractState .readPointer)
        (proposal.2 .readCounter).nextState
      rw [show (fun | .stored => nextContractState .readPointer) =
          (childContracts element addressWidth .readCounter).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .readCounter)
            (fun | .stored => contractState .readPointer) by
        funext statePort
        cases statePort
        change nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
            (contractState .readPointer) (contractState .writePointer) =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            ((proposal.2 .control).outputs .readAdvance) (inputs .reset)
            (contractState .readPointer)
        rw [controlReadAdvance]
        rfl]
      exact readNextCorresponds
    · change (layerChildren .writeCounter).certification.stateCorresponds
        (fun | .stored => nextContractState .writePointer)
        (proposal.2 .writeCounter).nextState
      rw [show (fun | .stored => nextContractState .writePointer) =
          (childContracts element addressWidth .writeCounter).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .writeCounter)
            (fun | .stored => contractState .writePointer) by
        funext statePort
        cases statePort
        change nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
            (contractState .readPointer) (contractState .writePointer) =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            ((proposal.2 .control).outputs .writeAdvance) (inputs .reset)
            (contractState .writePointer)
        rw [controlWriteAdvance]
        rfl]
      exact writeNextCorresponds
    · change (layerChildren .storage).certification.stateCorresponds
        (fun | .entries => nextContractState .entries)
        (proposal.2 .storage).nextState
      rw [show (fun | .entries => nextContractState .entries) =
          (childContracts element addressWidth .storage).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .storage)
            (fun | .entries => contractState .entries) by
        funext statePort
        cases statePort
        change nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
            (contractState .readPointer) (contractState .writePointer)
            (contractState .entries) =
          RegisterBank.nextEntries addressWidth
            ((proposal.2 .control).outputs .writeAdvance)
            ((proposal.2 .control).outputs .writeAddress)
            (inputs .inputData) (contractState .entries)
        rw [controlWriteAdvance, controlWriteAddress]
        rfl]
      exact storageNextCorresponds

end LayerCertification

/-- The FIFO wiring implements its cycle contract for any counters, control,
and storage hierarchy satisfying the declared child contracts. -/
noncomputable opaque certifiedLayer (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body element addressWidth) (childContracts element addressWidth)
      (cycleContract element addressWidth) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules element addressWidth) (coversChildren element addressWidth)
    (stateCorresponds element addressWidth)
    (hasCorrespondingState element addressWidth) (implements element addressWidth)

@[reducible] private noncomputable def certifiedChildren
    (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body element addressWidth) (childContracts element addressWidth)
  | .readCounter | .writeCounter =>
      (EnabledResetCounter.certified (addressWidth + 1)
        (zeroPointer addressWidth)).certifiedStructure
  | .control => (Fifo.PointerControl.certified addressWidth).certifiedStructure
  | .storage => (RegisterBank.certified element addressWidth 1).certifiedStructure

private noncomputable opaque certification (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure element addressWidth)
      (cycleContract element addressWidth) :=
  (certifiedLayer element addressWidth).certifyComposite
    (structuralChildren element addressWidth)
    (certifiedChildren element addressWidth) (by
      intro child
      cases child with
      | readCounter | writeCounter =>
          exact EnabledResetCounter.certified_moduleStructure
            (addressWidth + 1) (zeroPointer addressWidth)
      | control => exact Fifo.PointerControl.certified_moduleStructure addressWidth
      | storage => exact RegisterBank.certified_moduleStructure element addressWidth 1)

noncomputable def certified (element : SignalType) (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports element) :=
  (certification element addressWidth).bundle

@[simp] theorem certified_moduleStructure (element : SignalType)
    (addressWidth : Nat) :
    (certified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem certified_cycleContract (element : SignalType)
    (addressWidth : Nat) :
    (certified element addressWidth).cycleContract =
      cycleContract element addressWidth := rfl

end Silean.Modules.Fifo

namespace Silean.Modules.Fifo.Naming

open Silean Silean.Interfaces.Fifo Silean.Naming

def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.Fifo.moduleStructure element addressWidth) := by
  unfold Modules.Fifo.moduleStructure
  exact .composite
    ⟨"fifo", "structural", [.shape element, .natural addressWidth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming element elementNaming)
    (fun
      | .readCounter => "read_pointer"
      | .writeCounter => "write_pointer"
      | .control => "pointer_control"
      | .storage => "storage")
    (fun
      | .readCounter | .writeCounter =>
          EnabledResetCounter.Naming.naming (addressWidth + 1)
            (Modules.Fifo.zeroPointer addressWidth)
      | .control => Fifo.PointerControl.Naming.naming addressWidth
      | .storage => RegisterBank.Naming.namingWith element addressWidth 1 elementNaming)

def naming (element : SignalType) (addressWidth : Nat) :
    ModuleNaming (Modules.Fifo.moduleStructure element addressWidth) :=
  namingWith element addressWidth (.positional element)

end Silean.Modules.Fifo.Naming
