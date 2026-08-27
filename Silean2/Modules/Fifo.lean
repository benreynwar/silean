import Silean2.CertifiedSchedule
import Silean2.Modules.EnabledResetCounter
import Silean2.Modules.FifoInterface
import Silean2.Modules.FifoPointerControl
import Silean2.Modules.RegisterBank

namespace Silean2.Modules.Fifo

open Silean2

abbrev Pointer (addressWidth : Nat) :=
  EnabledResetCounter.Value (addressWidth + 1)

abbrev Entries (element : SignalType) (addressWidth : Nat) :=
  Fin (RegisterBank.entryCount addressWidth) → element.Denote

@[reducible] def pointerType (addressWidth : Nat) : SignalType :=
  .vector (addressWidth + 1) .bit

def zeroPointer (addressWidth : Nat) : Pointer addressWidth := fun _ => false

inductive State
  | readPointer
  | writePointer
  | entries
deriving Enumeration

@[reducible] def stateMap (element : SignalType) (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of State fun
    | .readPointer | .writePointer => pointerType addressWidth
    | .entries => .vector (RegisterBank.entryCount addressWidth) element

def inputReady (readPointer writePointer : Pointer addressWidth) : Bool :=
  FifoPointerControl.inputReady readPointer writePointer

def outputValid (readPointer writePointer : Pointer addressWidth) : Bool :=
  FifoPointerControl.outputValid readPointer writePointer

def outputData (addressWidth : Nat) (readPointer : Pointer addressWidth)
    (entries : Entries element addressWidth) : element.Denote :=
  entries (BitVector.toIndex addressWidth
    (FifoPointerControl.pointerAddress readPointer))

def readAdvance (readPointer writePointer : Pointer addressWidth)
    (ready : Bool) : Bool :=
  FifoPointerControl.readAdvance readPointer writePointer ready

def writeAdvance (readPointer writePointer : Pointer addressWidth)
    (valid : Bool) : Bool :=
  FifoPointerControl.writeAdvance readPointer writePointer valid

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
    (FifoPointerControl.pointerAddress writePointer) data entries

inductive Rule | observe
deriving Enumeration

def outputRule (element : SignalType) (addressWidth : Nat) :
    CycleOutputRule (ports element) (stateMap element addressWidth)
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
    CycleStateRule (ports element) (stateMap element addressWidth) where
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
    ModuleCycleContract (ports element) where
  state := stateMap element addressWidth
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule element addressWidth⟩
  stateRule := stateRule element addressWidth
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element).outputs.Values) :
    (outputRule element addressWidth).Holds inputs state outputs ↔
      outputs .outputValid = outputValid (state .readPointer) (state .writePointer) ∧
      outputs .outputData = outputData addressWidth (state .readPointer) (state .entries) ∧
      outputs .inputReady = inputReady (state .readPointer) (state .writePointer) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
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
  have empty := (FifoPointerControl.empty_eq_true_iff pointer pointer).mpr rfl
  simp [outputValid, inputReady, FifoPointerControl.outputValid,
    FifoPointerControl.inputReady, empty,
    FifoPointerControl.empty_implies_not_full pointer pointer empty]

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
        (FifoPointerControl.pointerAddress writePointer)) = data := by
  unfold nextEntries
  rw [accepted]
  exact RegisterBank.nextEntries_selected _ _ _ _

private inductive Instance
  | readCounter
  | writeCounter
  | control
  | storage
deriving Enumeration

@[reducible] private def instances (element : SignalType)
    (addressWidth : Nat) : Instances :=
  EnumeratedMap.of Instance fun
    | .readCounter | .writeCounter =>
        EnabledResetCounter.ports (addressWidth + 1)
    | .control => FifoPointerControl.ports addressWidth
    | .storage => RegisterBank.ports element addressWidth

@[reducible] private def context (element : SignalType)
    (addressWidth : Nat) : EndpointContext where
  ports := ports element
  instances := instances element addressWidth

private def wiring (element : SignalType) (addressWidth : Nat) :
    Wiring (context element addressWidth).ports
      (context element addressWidth).instances where
  moduleOutput
    | .outputValid => (context element addressWidth).instanceOutput .control .outputValid
    | .outputData => (context element addressWidth).instanceOutput .storage .readValue
    | .inputReady => (context element addressWidth).instanceOutput .control .inputReady
  instanceInput
    | .readCounter, .enable =>
        (context element addressWidth).instanceOutput .control .readAdvance
    | .readCounter, .reset => (context element addressWidth).moduleInput .reset
    | .writeCounter, .enable =>
        (context element addressWidth).instanceOutput .control .writeAdvance
    | .writeCounter, .reset => (context element addressWidth).moduleInput .reset
    | .control, .readPointer =>
        (context element addressWidth).instanceOutput .readCounter .value
    | .control, .writePointer =>
        (context element addressWidth).instanceOutput .writeCounter .value
    | .control, .inputValid => (context element addressWidth).moduleInput .inputValid
    | .control, .outputReady => (context element addressWidth).moduleInput .outputReady
    | .storage, .writeEnable =>
        (context element addressWidth).instanceOutput .control .writeAdvance
    | .storage, .writeAddress =>
        (context element addressWidth).instanceOutput .control .writeAddress
    | .storage, .writeValue => (context element addressWidth).moduleInput .inputData
    | .storage, .readAddress =>
        (context element addressWidth).instanceOutput .control .readAddress

@[reducible] private def body (element : SignalType) (addressWidth : Nat) : ModuleBody :=
  ⟨context element addressWidth, wiring element addressWidth⟩

@[reducible] private noncomputable def children (element : SignalType)
    (addressWidth : Nat) : Certified.Children (body element addressWidth)
  | .readCounter | .writeCounter =>
      EnabledResetCounter.certified (addressWidth + 1) (zeroPointer addressWidth)
  | .control => FifoPointerControl.certified addressWidth
  | .storage => RegisterBank.certified element addressWidth

@[reducible] private def structuralChildren (element : SignalType)
    (addressWidth : Nat) :
    (name : (instances element addressWidth).Name) →
      ModuleStructure ((instances element addressWidth).ports name)
  | .readCounter | .writeCounter =>
      EnabledResetCounter.moduleStructure (addressWidth + 1) (zeroPointer addressWidth)
  | .control => FifoPointerControl.moduleStructure addressWidth
  | .storage => RegisterBank.moduleStructure element addressWidth

def moduleStructure (element : SignalType) (addressWidth : Nat) :
    ModuleStructure (ports element) :=
  .composite (body element addressWidth) (structuralChildren element addressWidth)

private theorem moduleStructure_eq (element : SignalType) (addressWidth : Nat) :
    moduleStructure element addressWidth =
      Certified.moduleStructure (body element addressWidth)
        (children element addressWidth) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

@[reducible] private noncomputable def childStructure (element : SignalType)
    (addressWidth : Nat) := Certified.childStructure (children element addressWidth)

private abbrev readCounterRule (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.readCounter, EnabledResetCounter.Rule.observe⟩

private abbrev writeCounterRule (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.writeCounter, EnabledResetCounter.Rule.observe⟩

private abbrev controlRule (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.control, FifoPointerControl.Rule.apply⟩

private abbrev storageRule (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.storage, RegisterBank.Rule.read⟩

@[simp] private theorem readCounterRule_reads (element : SignalType)
    (addressWidth : Nat) : (readCounterRule element addressWidth).reads = [] := rfl
@[simp] private theorem writeCounterRule_reads (element : SignalType)
    (addressWidth : Nat) : (writeCounterRule element addressWidth).reads = [] := rfl
@[simp] private theorem controlRule_reads (element : SignalType)
    (addressWidth : Nat) :
    (controlRule element addressWidth).reads =
      [.readPointer, .writePointer, .inputValid, .outputReady] := rfl
@[simp] private theorem storageRule_reads (element : SignalType)
    (addressWidth : Nat) : (storageRule element addressWidth).reads = [.readAddress] := rfl
@[simp] private theorem readCounterRule_writes (element : SignalType)
    (addressWidth : Nat) : (readCounterRule element addressWidth).writes = [.value] := rfl
@[simp] private theorem writeCounterRule_writes (element : SignalType)
    (addressWidth : Nat) : (writeCounterRule element addressWidth).writes = [.value] := rfl
@[simp] private theorem controlRule_writes (element : SignalType)
    (addressWidth : Nat) :
    (controlRule element addressWidth).writes =
      [.readAddress, .writeAddress, .inputReady, .outputValid,
        .readAdvance, .writeAdvance] := rfl
@[simp] private theorem storageRule_writes (element : SignalType)
    (addressWidth : Nat) : (storageRule element addressWidth).writes = [.readValue] := rfl

private def outputSchedule (element : SignalType) (addressWidth : Nat) :
    Certified.OutputSchedule (body element addressWidth)
      (children element addressWidth) (cycleContract element addressWidth) .observe :=
  .call (readCounterRule element addressWidth)
    (by intro input member; rw [readCounterRule_reads] at member; cases member)
    (by simp)
  (.call (writeCounterRule element addressWidth)
    (by intro input member; rw [writeCounterRule_reads] at member; cases member)
    (by simp)
  (.call (controlRule element addressWidth)
    (by
      intro input _
      cases input with
      | readPointer => exact ⟨EnabledResetCounter.Rule.observe, by simp,
          by simp [readCounterRule_writes]⟩
      | writePointer => exact ⟨EnabledResetCounter.Rule.observe, by simp,
          by simp [writeCounterRule_writes]⟩
      | inputValid =>
          change Input.inputValid ∈
            (outputRule element addressWidth).readsInputs.labels
          simp [outputRule, SignalMap.select, SignalSelection.labels,
            SignalSelection.prepend]
      | outputReady =>
          change Input.outputReady ∈
            (outputRule element addressWidth).readsInputs.labels
          simp [outputRule, SignalMap.select, SignalSelection.labels,
            SignalSelection.prepend])
    (by simp)
  (.call (storageRule element addressWidth)
    (by
      intro input member
      rw [storageRule_reads] at member
      simp only [List.mem_singleton] at member
      subst input
      exact ⟨FifoPointerControl.Rule.apply, by simp,
        by simp [controlRule_writes]⟩)
    (by simp)
    (.done (by
      intro output _
      cases output with
      | outputValid | inputReady =>
          exact ⟨FifoPointerControl.Rule.apply, by simp,
            by simp [controlRule_writes]⟩
      | outputData => exact ⟨RegisterBank.Rule.read, by simp,
          by simp [storageRule_writes]⟩)))))

private def stateSchedule (element : SignalType) (addressWidth : Nat) :
    Certified.StateSchedule (body element addressWidth)
      (children element addressWidth) :=
  .call (readCounterRule element addressWidth)
    (by intros; trivial) (by simp)
  (.call (writeCounterRule element addressWidth)
    (by intros; trivial) (by simp)
  (.call (controlRule element addressWidth)
    (by
      intro input _
      cases input with
      | readPointer => exact ⟨EnabledResetCounter.Rule.observe, by simp,
          by simp [readCounterRule_writes]⟩
      | writePointer => exact ⟨EnabledResetCounter.Rule.observe, by simp,
          by simp [writeCounterRule_writes]⟩
      | inputValid | outputReady => trivial)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | readCounter =>
        cases input with
        | enable => exact ⟨FifoPointerControl.Rule.apply, by simp,
            by simp [controlRule_writes]⟩
        | reset => trivial
    | writeCounter =>
        cases input with
        | enable => exact ⟨FifoPointerControl.Rule.apply, by simp,
            by simp [controlRule_writes]⟩
        | reset => trivial
    | control =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | storage =>
        cases input with
        | writeEnable | writeAddress =>
            exact ⟨FifoPointerControl.Rule.apply, by simp,
              by simp [controlRule_writes]⟩
        | writeValue => trivial
        | readAddress =>
            change RegisterBank.Input.readAddress ∈
              (RegisterBank.stateRule element addressWidth).readsInputs.labels at member
            simp [RegisterBank.stateRule, SignalMap.select,
              SignalSelection.labels, SignalSelection.prepend] at member))))

private def ruleSchedules (element : SignalType) (addressWidth : Nat) :
    Certified.RuleSchedules (body element addressWidth)
      (children element addressWidth) (cycleContract element addressWidth) where
  output | .observe => outputSchedule element addressWidth
  state := stateSchedule element addressWidth

private theorem coversChildren (element : SignalType) (addressWidth : Nat) :
    (ruleSchedules element addressWidth).CoversChildren := by
  intro child rule
  cases child with
  | readCounter =>
      change EnabledResetCounter.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_includes
      change readCounterRule element addressWidth ∈
        (stateSchedule element addressWidth).finalAvailability
      simp [stateSchedule, Certified.Schedule.finalAvailability]
  | writeCounter =>
      change EnabledResetCounter.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_includes
      change writeCounterRule element addressWidth ∈
        (stateSchedule element addressWidth).finalAvailability
      simp [stateSchedule, Certified.Schedule.finalAvailability]
  | control =>
      change FifoPointerControl.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_includes
      change controlRule element addressWidth ∈
        (stateSchedule element addressWidth).finalAvailability
      simp [stateSchedule, Certified.Schedule.finalAvailability]
  | storage =>
      change RegisterBank.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (ruleSchedules element addressWidth) .observe
      change storageRule element addressWidth ∈
        (outputSchedule element addressWidth).finalAvailability
      simp [outputSchedule, Certified.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (element : SignalType) (addressWidth : Nat) :
    (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).HasAtMostOneSolution :=
  (ruleSchedules element addressWidth).hasAtMostOneSolution
    (coversChildren element addressWidth)

private def controlInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (readPointer writePointer : Pointer addressWidth) :
    (FifoPointerControl.ports addressWidth).inputs.Values
  | .readPointer => readPointer
  | .writePointer => writePointer
  | .inputValid => inputs .inputValid
  | .outputReady => inputs .outputReady

private def counterInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values) (enable : Bool) :
    (EnabledResetCounter.ports (addressWidth + 1)).inputs.Values
  | .enable => enable
  | .reset => inputs .reset

private noncomputable def storageInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (control : ProposedValues (children element addressWidth .control).moduleStructure) :
    (RegisterBank.ports element addressWidth).inputs.Values
  | .writeEnable => control.outputs .writeAdvance
  | .writeAddress => control.outputs .writeAddress
  | .writeValue => inputs .inputData
  | .readAddress => control.outputs .readAddress

private theorem hasStructuralResult (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (currentState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) :
    ∃ proposal, (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).IsSolution inputs currentState proposal := by
  rcases (children element addressWidth .readCounter).hasCorrespondingState
      (currentState .readCounter) with ⟨readState, readCorresponds⟩
  rcases (children element addressWidth .writeCounter).hasCorrespondingState
      (currentState .writeCounter) with ⟨writeState, writeCorresponds⟩
  rcases (children element addressWidth .control).hasStructuralResult
      (controlInputs element addressWidth inputs
        (readState .stored) (writeState .stored))
      (currentState .control) with ⟨control, controlSatisfies⟩
  rcases (children element addressWidth .readCounter).hasStructuralResult
      (counterInputs element addressWidth inputs (control.outputs .readAdvance))
      (currentState .readCounter) with ⟨readCounter, readCounterSatisfies⟩
  rcases (children element addressWidth .writeCounter).hasStructuralResult
      (counterInputs element addressWidth inputs (control.outputs .writeAdvance))
      (currentState .writeCounter) with ⟨writeCounter, writeCounterSatisfies⟩
  rcases (children element addressWidth .storage).hasStructuralResult
      (storageInputs element addressWidth inputs control)
      (currentState .storage) with ⟨storage, storageSatisfies⟩
  have readOutput : readCounter.outputs .value = readState .stored := by
    rcases (children element addressWidth .readCounter).implements
        _ readState _ readCounter readCorresponds readCounterSatisfies with
      ⟨_, evaluates, _⟩
    exact (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (evaluates.1 EnabledResetCounter.Rule.observe)
  have writeOutput : writeCounter.outputs .value = writeState .stored := by
    rcases (children element addressWidth .writeCounter).implements
        _ writeState _ writeCounter writeCorresponds writeCounterSatisfies with
      ⟨_, evaluates, _⟩
    exact (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (evaluates.1 EnabledResetCounter.Rule.observe)
  let proposals : (name : Instance) →
      ProposedValues (childStructure element addressWidth name)
    | .readCounter => readCounter
    | .writeCounter => writeCounter
    | .control => control
    | .storage => storage
  let outputs : (ports element).outputs.Values := fun
    | .outputValid => control.outputs .outputValid
    | .outputData => storage.outputs .readValue
    | .inputReady => control.outputs .inputReady
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | readCounter =>
        change (children element addressWidth .readCounter).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposals .readCounter)
          (currentState .readCounter) readCounter
        rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposals .readCounter =
            counterInputs element addressWidth inputs (control.outputs .readAdvance) by
          funext port; cases port <;> rfl]
        exact readCounterSatisfies
    | writeCounter =>
        change (children element addressWidth .writeCounter).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposals .writeCounter)
          (currentState .writeCounter) writeCounter
        rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposals .writeCounter =
            counterInputs element addressWidth inputs (control.outputs .writeAdvance) by
          funext port; cases port <;> rfl]
        exact writeCounterSatisfies
    | control =>
        change (children element addressWidth .control).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposals .control)
          (currentState .control) control
        rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposals .control =
            controlInputs element addressWidth inputs
              (readState .stored) (writeState .stored) by
          funext port
          cases port with
          | readPointer => exact readOutput
          | writePointer => exact writeOutput
          | inputValid | outputReady => rfl]
        exact controlSatisfies
    | storage =>
        change (children element addressWidth .storage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposals .storage)
          (currentState .storage) storage
        rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposals .storage =
            storageInputs element addressWidth inputs control by
          funext port; cases port <;> rfl]
        exact storageSatisfies

private def stateCorresponds (element : SignalType) (addressWidth : Nat)
    (contractState : (stateMap element addressWidth).Values)
    (structuralState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) : Prop :=
  (children element addressWidth .readCounter).stateCorresponds
      (fun | .stored => contractState .readPointer) (structuralState .readCounter) ∧
  (children element addressWidth .writeCounter).stateCorresponds
      (fun | .stored => contractState .writePointer) (structuralState .writeCounter) ∧
  (children element addressWidth .storage).stateCorresponds
      (fun | .entries => contractState .entries) (structuralState .storage)

private theorem hasCorrespondingState (element : SignalType) (addressWidth : Nat)
    (structuralState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) :
    ∃ contractState, stateCorresponds element addressWidth contractState structuralState := by
  rcases (children element addressWidth .readCounter).hasCorrespondingState
      (structuralState .readCounter) with ⟨readState, readCorresponds⟩
  rcases (children element addressWidth .writeCounter).hasCorrespondingState
      (structuralState .writeCounter) with ⟨writeState, writeCorresponds⟩
  rcases (children element addressWidth .storage).hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  let contractState : (stateMap element addressWidth).Values := fun
    | .readPointer => readState .stored
    | .writePointer => writeState .stored
    | .entries => storageState .entries
  exact ⟨contractState, readCorresponds, writeCorresponds, storageCorresponds⟩

private theorem implements (element : SignalType) (addressWidth : Nat) :
    Implements (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)) (cycleContract element addressWidth)
      (stateCorresponds element addressWidth) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases corresponds with ⟨readCorresponds, writeCorresponds, storageCorresponds⟩
  have readMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies
      .readCounter (fun | .stored => contractState .readPointer) readCorresponds
  have writeMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies
      .writeCounter (fun | .stored => contractState .writePointer) writeCorresponds
  have storageMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies
      .storage (fun | .entries => contractState .entries) storageCorresponds
  rcases (children element addressWidth .control).hasCorrespondingState
      (structuralState .control) with ⟨controlState, controlCorresponds⟩
  have controlState_eq : controlState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst controlState
  have controlMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies
      .control SignalMap.emptyValues controlCorresponds
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
    (FifoPointerControl.outputRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 FifoPointerControl.Rule.apply)
  have controlInputRead : ProposedValues.childInputs (body element addressWidth)
      (childStructure element addressWidth) inputs proposal.2 .control .readPointer =
      (proposal.2 .readCounter).outputs .value := rfl
  have controlInputWrite : ProposedValues.childInputs (body element addressWidth)
      (childStructure element addressWidth) inputs proposal.2 .control .writePointer =
      (proposal.2 .writeCounter).outputs .value := rfl
  have controlInputValid : ProposedValues.childInputs (body element addressWidth)
      (childStructure element addressWidth) inputs proposal.2 .control .inputValid =
      inputs .inputValid := rfl
  have controlOutputReady : ProposedValues.childInputs (body element addressWidth)
      (childStructure element addressWidth) inputs proposal.2 .control .outputReady =
      inputs .outputReady := rfl
  have controlReadAddress : (proposal.2 .control).outputs .readAddress =
      FifoPointerControl.pointerAddress (contractState .readPointer) := by
    rw [controlValues.1]
    exact congrArg FifoPointerControl.pointerAddress readCurrent
  have controlWriteAddress : (proposal.2 .control).outputs .writeAddress =
      FifoPointerControl.pointerAddress (contractState .writePointer) := by
    rw [controlValues.2.1]
    exact congrArg FifoPointerControl.pointerAddress writeCurrent
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
  have storageRead : (proposal.2 .storage).outputs .readValue =
      outputData addressWidth (contractState .readPointer)
        (contractState .entries) := by
    have held := (RegisterBank.readRule_holds_iff element addressWidth _ _ _).mp
      (storageEvaluates.1 RegisterBank.Rule.read)
    rw [held]
    unfold outputData
    rw [show (ProposedValues.childInputs (body element addressWidth)
      (childStructure element addressWidth) inputs proposal.2 .storage) .readAddress =
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
    · change (children element addressWidth .readCounter).stateCorresponds
        (fun | .stored => nextContractState .readPointer)
        (proposal.2 .readCounter).nextState
      rw [show (fun | .stored => nextContractState .readPointer) =
          (children element addressWidth .readCounter).cycleContract.stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (childStructure element addressWidth) inputs proposal.2 .readCounter)
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
    · change (children element addressWidth .writeCounter).stateCorresponds
        (fun | .stored => nextContractState .writePointer)
        (proposal.2 .writeCounter).nextState
      rw [show (fun | .stored => nextContractState .writePointer) =
          (children element addressWidth .writeCounter).cycleContract.stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (childStructure element addressWidth) inputs proposal.2 .writeCounter)
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
    · change (children element addressWidth .storage).stateCorresponds
        (fun | .entries => nextContractState .entries)
        (proposal.2 .storage).nextState
      rw [show (fun | .entries => nextContractState .entries) =
          (children element addressWidth .storage).cycleContract.stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (childStructure element addressWidth) inputs proposal.2 .storage)
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

private noncomputable def proofCertification (element : SignalType)
    (addressWidth : Nat) :
    ModuleCycleCertification
      (Certified.moduleStructure (body element addressWidth)
        (children element addressWidth))
      (cycleContract element addressWidth) where
  stateCorresponds := stateCorresponds element addressWidth
  hasCorrespondingState := hasCorrespondingState element addressWidth
  hasStructuralResult := hasStructuralResult element addressWidth
  structuralResultUnique := hasAtMostOneSolution element addressWidth
  implements := implements element addressWidth

private noncomputable opaque certification (element : SignalType)
    (addressWidth : Nat) :
    ModuleCycleCertification (moduleStructure element addressWidth)
      (cycleContract element addressWidth) :=
  (proofCertification element addressWidth).transportStructure
    (moduleStructure_eq element addressWidth).symm

noncomputable def certified (element : SignalType) (addressWidth : Nat) :
    ModuleCycleCertified (ports element) :=
  (certification element addressWidth).bundle

@[simp] theorem certified_moduleStructure (element : SignalType)
    (addressWidth : Nat) :
    (certified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem certified_cycleContract (element : SignalType)
    (addressWidth : Nat) :
    (certified element addressWidth).cycleContract =
      cycleContract element addressWidth := rfl

end Silean2.Modules.Fifo

namespace Silean2.Modules.Fifo.Naming

open Silean2 Silean2.Naming

def portsWithNaming (element : SignalType) (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.Fifo.ports element) where
  inputs := ⟨fun
    | .inputValid => "input_valid"
    | .inputData => "input_data"
    | .outputReady => "output_ready"
    | .reset => "reset"⟩
  outputs := ⟨fun
    | .outputValid => "output_valid"
    | .outputData => "output_data"
    | .inputReady => "input_ready"⟩
  inputTypes := fun
    | .inputValid | .outputReady | .reset => .bit
    | .inputData => elementNaming
  outputTypes := fun
    | .outputValid | .inputReady => .bit
    | .outputData => elementNaming

def ports (element : SignalType) :
    ModulePortsNaming (Modules.Fifo.ports element) :=
  portsWithNaming element (.positional element)

def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.Fifo.moduleStructure element addressWidth) := by
  unfold Modules.Fifo.moduleStructure
  exact .composite
    ⟨"fifo", "structural", [.shape element, .natural addressWidth]⟩
    (portsWithNaming element elementNaming)
    (fun
      | .readCounter => "read_pointer"
      | .writeCounter => "write_pointer"
      | .control => "pointer_control"
      | .storage => "storage")
    (fun
      | .readCounter | .writeCounter =>
          EnabledResetCounter.Naming.naming (addressWidth + 1)
            (Modules.Fifo.zeroPointer addressWidth)
      | .control => FifoPointerControl.Naming.naming addressWidth
      | .storage => RegisterBank.Naming.namingWith element addressWidth elementNaming)

def naming (element : SignalType) (addressWidth : Nat) :
    ModuleNaming (Modules.Fifo.moduleStructure element addressWidth) :=
  namingWith element addressWidth (.positional element)

end Silean2.Modules.Fifo.Naming
