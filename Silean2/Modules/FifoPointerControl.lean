import Silean2.CertifiedSchedule
import Silean2.ModuleCycleEvaluation
import Silean2.Naming.ModuleNaming
import Silean2.Naming.PrimitiveNaming
import Silean2.Naming.SignalAdapterNaming
import Silean2.Modules.Equality
import Silean2.Primitives
import Silean2.SignalAdapterCertified
import Silean2.SignalLogic

namespace Silean2.Modules.FifoPointerControl

open Silean2

abbrev Pointer (addressWidth : Nat) := Fin (addressWidth + 1) → Bool
abbrev Address (addressWidth : Nat) := Fin addressWidth → Bool

@[reducible] def pointerType (addressWidth : Nat) : SignalType :=
  .vector (addressWidth + 1) .bit

@[reducible] def addressType (addressWidth : Nat) : SignalType :=
  .vector addressWidth .bit

def pointerAddress (pointer : Pointer addressWidth) : Address addressWidth :=
  fun index => pointer index.castSucc

def pointerWrap (pointer : Pointer addressWidth) : Bool :=
  pointer (Fin.last addressWidth)

def addressesEqual (readPointer writePointer : Pointer addressWidth) : Bool :=
  (addressType addressWidth).equal
    (pointerAddress readPointer) (pointerAddress writePointer)

def wrapsEqual (readPointer writePointer : Pointer addressWidth) : Bool :=
  SignalType.bit.equal (pointerWrap readPointer) (pointerWrap writePointer)

def wrapsDiffer (readPointer writePointer : Pointer addressWidth) : Bool :=
  !(wrapsEqual readPointer writePointer)

def empty (readPointer writePointer : Pointer addressWidth) : Bool :=
  addressesEqual readPointer writePointer && wrapsEqual readPointer writePointer

def full (readPointer writePointer : Pointer addressWidth) : Bool :=
  addressesEqual readPointer writePointer && wrapsDiffer readPointer writePointer

def inputReady (readPointer writePointer : Pointer addressWidth) : Bool :=
  !(full readPointer writePointer)

def outputValid (readPointer writePointer : Pointer addressWidth) : Bool :=
  !(empty readPointer writePointer)

def readAdvance (readPointer writePointer : Pointer addressWidth)
    (downstreamReady : Bool) : Bool :=
  outputValid readPointer writePointer && downstreamReady

def writeAdvance (readPointer writePointer : Pointer addressWidth)
    (upstreamValid : Bool) : Bool :=
  upstreamValid && inputReady readPointer writePointer

inductive Input
  | readPointer
  | writePointer
  | inputValid
  | outputReady
deriving Enumeration

inductive Output
  | readAddress
  | writeAddress
  | inputReady
  | outputValid
  | readAdvance
  | writeAdvance
deriving Enumeration

@[reducible] def inputMap (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .readPointer | .writePointer => pointerType addressWidth
    | .inputValid | .outputReady => .bit

@[reducible] def outputMap (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .readAddress | .writeAddress => addressType addressWidth
    | .inputReady | .outputValid | .readAdvance | .writeAdvance => .bit

@[reducible] def ports (addressWidth : Nat) : ModulePorts :=
  ⟨inputMap addressWidth, outputMap addressWidth⟩

inductive Rule | apply
deriving Enumeration

def outputRule (addressWidth : Nat) :
    CycleOutputRule (ports addressWidth) emptySignalMap
      { inputTypes := .cons (pointerType addressWidth)
          (.cons (pointerType addressWidth) (.cons .bit (.cons .bit .nil)))
        outputTypes := .cons (addressType addressWidth)
          (.cons (addressType addressWidth)
            (.cons .bit (.cons .bit (.cons .bit (.cons .bit .nil))))) } where
  readsInputs := (((inputMap addressWidth).select .outputReady).prepend
    .inputValid).prepend .writePointer |>.prepend .readPointer
  writesOutputs := (((((outputMap addressWidth).select .writeAdvance).prepend
    .readAdvance).prepend .outputValid).prepend .inputReady).prepend
    .writeAddress |>.prepend .readAddress
  target
    | (readPointer, (writePointer, (inputValid, (outputReady, ())))), _ =>
        (pointerAddress readPointer,
          (pointerAddress writePointer,
            (inputReady readPointer writePointer,
              (outputValid readPointer writePointer,
                (readAdvance readPointer writePointer outputReady,
                  (writeAdvance readPointer writePointer inputValid, ()))))))

@[reducible] def cycleContract (addressWidth : Nat) :
    ModuleCycleContract (ports addressWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule addressWidth⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (addressWidth : Nat)
    (inputs : (ports addressWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports addressWidth).outputs.Values) :
    (outputRule addressWidth).Holds inputs state outputs ↔
      outputs .readAddress = pointerAddress (inputs .readPointer) ∧
      outputs .writeAddress = pointerAddress (inputs .writePointer) ∧
      outputs .inputReady = inputReady (inputs .readPointer) (inputs .writePointer) ∧
      outputs .outputValid = outputValid (inputs .readPointer) (inputs .writePointer) ∧
      outputs .readAdvance = readAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .outputReady) ∧
      outputs .writeAdvance = writeAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .inputValid) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem addressesEqual_eq_true_iff (readPointer writePointer : Pointer addressWidth) :
    addressesEqual readPointer writePointer = true ↔
      pointerAddress readPointer = pointerAddress writePointer := by
  exact (addressType addressWidth).equal_eq_true_iff _ _

theorem empty_eq_true_iff (readPointer writePointer : Pointer addressWidth) :
    empty readPointer writePointer = true ↔ readPointer = writePointer := by
  simp only [empty, Bool.and_eq_true, addressesEqual_eq_true_iff]
  constructor
  · rintro ⟨addresses, wraps⟩
    funext index
    by_cases isWrap : index = Fin.last addressWidth
    · subst index
      have sameWrap := (SignalType.equal_eq_true_iff .bit _ _).mp wraps
      change readPointer (Fin.last addressWidth) =
        writePointer (Fin.last addressWidth) at sameWrap
      exact sameWrap
    · have notLastValue : index.val ≠ addressWidth := by
        intro equality
        apply isWrap
        apply Fin.ext
        simpa using equality
      have below : index.val < addressWidth := by omega
      let addressIndex : Fin addressWidth := ⟨index.val, below⟩
      have sameAddress := congrFun addresses addressIndex
      simpa [pointerAddress, addressIndex] using sameAddress
  · intro pointers
    subst writePointer
    constructor
    · rfl
    · exact (SignalType.equal_eq_true_iff .bit _ _).mpr rfl

theorem wrapsDiffer_eq_true_iff (readPointer writePointer : Pointer addressWidth) :
    wrapsDiffer readPointer writePointer = true ↔
      pointerWrap readPointer ≠ pointerWrap writePointer := by
  cases readWrap : pointerWrap readPointer <;>
    cases writeWrap : pointerWrap writePointer <;>
      change readPointer (Fin.last addressWidth) = _ at readWrap <;>
      change writePointer (Fin.last addressWidth) = _ at writeWrap <;>
      simp [wrapsDiffer, wrapsEqual, SignalType.equal, pointerWrap,
        readWrap, writeWrap]

theorem wrapsEqual_eq_true_iff (readPointer writePointer : Pointer addressWidth) :
    wrapsEqual readPointer writePointer = true ↔
      pointerWrap readPointer = pointerWrap writePointer := by
  change SignalType.bit.equal _ _ = true ↔
    @Eq SignalType.bit.Denote _ _
  exact SignalType.equal_eq_true_iff .bit _ _

theorem full_eq_true_iff (readPointer writePointer : Pointer addressWidth) :
    full readPointer writePointer = true ↔
      pointerAddress readPointer = pointerAddress writePointer ∧
        pointerWrap readPointer ≠ pointerWrap writePointer := by
  simp [full, addressesEqual_eq_true_iff, wrapsDiffer_eq_true_iff]

theorem empty_implies_not_full (readPointer writePointer : Pointer addressWidth)
    (isEmpty : empty readPointer writePointer = true) :
    full readPointer writePointer = false := by
  have pointersEqual := (empty_eq_true_iff readPointer writePointer).mp isEmpty
  subst writePointer
  have addressSelf : addressesEqual readPointer readPointer = true :=
    (addressesEqual_eq_true_iff _ _).mpr rfl
  have wrapSelf : wrapsEqual readPointer readPointer = true := by
    exact (SignalType.equal_eq_true_iff .bit _ _).mpr rfl
  simp [full, wrapsDiffer, addressSelf, wrapSelf]

theorem full_implies_not_empty (readPointer writePointer : Pointer addressWidth)
    (isFull : full readPointer writePointer = true) :
    empty readPointer writePointer = false := by
  have fullParts := (full_eq_true_iff readPointer writePointer).mp isFull
  cases isEmpty : empty readPointer writePointer with
  | false => rfl
  | true =>
      have pointersEqual := (empty_eq_true_iff readPointer writePointer).mp isEmpty
      exact False.elim (fullParts.2 (congrFun pointersEqual (Fin.last addressWidth)))

theorem inputReady_eq_not_full (readPointer writePointer : Pointer addressWidth) :
    inputReady readPointer writePointer = !(full readPointer writePointer) := rfl

theorem outputValid_eq_not_empty (readPointer writePointer : Pointer addressWidth) :
    outputValid readPointer writePointer = !(empty readPointer writePointer) := rfl

theorem readAdvance_eq_true_iff (readPointer writePointer : Pointer addressWidth)
    (downstreamReady : Bool) :
    readAdvance readPointer writePointer downstreamReady = true ↔
      outputValid readPointer writePointer = true ∧ downstreamReady = true := by
  simp [readAdvance]

theorem writeAdvance_eq_true_iff (readPointer writePointer : Pointer addressWidth)
    (upstreamValid : Bool) :
    writeAdvance readPointer writePointer upstreamValid = true ↔
      upstreamValid = true ∧ inputReady readPointer writePointer = true := by
  simp [writeAdvance]

private def pointerSplitter (addressWidth : Nat) : SignalSplitter :=
  .vector (addressWidth + 1) .bit

private def addressCombiner (addressWidth : Nat) : SignalCombiner :=
  .vector addressWidth .bit

private inductive Instance
  | readSplit
  | writeSplit
  | readAddress
  | writeAddress
  | addressEquality
  | wrapEquality
  | wrapDifference
  | emptyGate
  | fullGate
  | readyInverter
  | validInverter
  | readGate
  | writeGate
deriving Enumeration

@[reducible] private def instances (addressWidth : Nat) : Instances :=
  EnumeratedMap.of Instance fun
    | .readSplit | .writeSplit => (pointerSplitter addressWidth).ports
    | .readAddress | .writeAddress => (addressCombiner addressWidth).ports
    | .addressEquality => Equality.ports (addressType addressWidth)
    | .wrapEquality => Primitives.eq.ports
    | .wrapDifference | .readyInverter | .validInverter => Primitives.not.ports
    | .emptyGate | .fullGate | .readGate | .writeGate => Primitives.and.ports

@[reducible] private def context (addressWidth : Nat) : EndpointContext where
  ports := ports addressWidth
  instances := instances addressWidth

private def wiring (addressWidth : Nat) :
    Wiring (context addressWidth).ports (context addressWidth).instances where
  moduleOutput
    | .readAddress => (context addressWidth).instanceOutput .readAddress .value
    | .writeAddress => (context addressWidth).instanceOutput .writeAddress .value
    | .inputReady => (context addressWidth).instanceOutput .readyInverter .output
    | .outputValid => (context addressWidth).instanceOutput .validInverter .output
    | .readAdvance => (context addressWidth).instanceOutput .readGate .output
    | .writeAdvance => (context addressWidth).instanceOutput .writeGate .output
  instanceInput
    | .readSplit, .value => (context addressWidth).moduleInput .readPointer
    | .writeSplit, .value => (context addressWidth).moduleInput .writePointer
    | .readAddress, index =>
        (context addressWidth).instanceOutput .readSplit index.castSucc
    | .writeAddress, index =>
        (context addressWidth).instanceOutput .writeSplit index.castSucc
    | .addressEquality, .left =>
        (context addressWidth).instanceOutput .readAddress .value
    | .addressEquality, .right =>
        (context addressWidth).instanceOutput .writeAddress .value
    | .wrapEquality, .left =>
        (context addressWidth).instanceOutput .readSplit (Fin.last addressWidth)
    | .wrapEquality, .right =>
        (context addressWidth).instanceOutput .writeSplit (Fin.last addressWidth)
    | .wrapDifference, .input =>
        (context addressWidth).instanceOutput .wrapEquality .output
    | .emptyGate, .left =>
        (context addressWidth).instanceOutput .addressEquality .result
    | .emptyGate, .right =>
        (context addressWidth).instanceOutput .wrapEquality .output
    | .fullGate, .left =>
        (context addressWidth).instanceOutput .addressEquality .result
    | .fullGate, .right =>
        (context addressWidth).instanceOutput .wrapDifference .output
    | .readyInverter, .input =>
        (context addressWidth).instanceOutput .fullGate .output
    | .validInverter, .input =>
        (context addressWidth).instanceOutput .emptyGate .output
    | .readGate, .left =>
        (context addressWidth).instanceOutput .validInverter .output
    | .readGate, .right => (context addressWidth).moduleInput .outputReady
    | .writeGate, .left => (context addressWidth).moduleInput .inputValid
    | .writeGate, .right =>
        (context addressWidth).instanceOutput .readyInverter .output

@[reducible] private def body (addressWidth : Nat) : ModuleBody :=
  ⟨context addressWidth, wiring addressWidth⟩

@[reducible] private noncomputable def children (addressWidth : Nat) :
    Certified.Children (body addressWidth)
  | .readSplit | .writeSplit => (pointerSplitter addressWidth).certified
  | .readAddress | .writeAddress => (addressCombiner addressWidth).certified
  | .addressEquality => Equality.certified (addressType addressWidth)
  | .wrapEquality => Primitives.eqCertified
  | .wrapDifference | .readyInverter | .validInverter => Primitives.notCertified
  | .emptyGate | .fullGate | .readGate | .writeGate => Primitives.andCertified

@[reducible] private noncomputable def childStructure (addressWidth : Nat) :=
  Certified.childStructure (children addressWidth)

@[reducible] private def structuralChildren (addressWidth : Nat) :
    (name : (instances addressWidth).Name) →
      ModuleStructure ((instances addressWidth).ports name)
  | .readSplit | .writeSplit => .splitter (pointerSplitter addressWidth)
  | .readAddress | .writeAddress => .combiner (addressCombiner addressWidth)
  | .addressEquality => Equality.moduleStructure (addressType addressWidth)
  | .wrapEquality => .primitive Primitives.eq
  | .wrapDifference | .readyInverter | .validInverter => .primitive Primitives.not
  | .emptyGate | .fullGate | .readGate | .writeGate => .primitive Primitives.and

def moduleStructure (addressWidth : Nat) : ModuleStructure (ports addressWidth) :=
  .composite (body addressWidth) (structuralChildren addressWidth)

private theorem moduleStructure_eq (addressWidth : Nat) :
    moduleStructure addressWidth =
      Certified.moduleStructure (body addressWidth) (children addressWidth) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

private abbrev occurrence (addressWidth : Nat) (child : Instance)
    (rule : (children addressWidth child).cycleContract.RuleName) :
    Certified.RuleOccurrence (children addressWidth) := ⟨child, rule⟩

private abbrev readSplitRule (addressWidth : Nat) :=
  occurrence addressWidth .readSplit SignalComponentRule.apply
private abbrev writeSplitRule (addressWidth : Nat) :=
  occurrence addressWidth .writeSplit SignalComponentRule.apply
private abbrev readAddressRule (addressWidth : Nat) :=
  occurrence addressWidth .readAddress SignalComponentRule.apply
private abbrev writeAddressRule (addressWidth : Nat) :=
  occurrence addressWidth .writeAddress SignalComponentRule.apply
private abbrev addressEqualityRule (addressWidth : Nat) :=
  occurrence addressWidth .addressEquality Equality.Rule.apply
private abbrev wrapEqualityRule (addressWidth : Nat) :=
  occurrence addressWidth .wrapEquality Primitives.EqRule.apply
private abbrev wrapDifferenceRule (addressWidth : Nat) :=
  occurrence addressWidth .wrapDifference Primitives.NotRule.apply
private abbrev emptyRule (addressWidth : Nat) :=
  occurrence addressWidth .emptyGate Primitives.AndRule.apply
private abbrev fullRule (addressWidth : Nat) :=
  occurrence addressWidth .fullGate Primitives.AndRule.apply
private abbrev readyRule (addressWidth : Nat) :=
  occurrence addressWidth .readyInverter Primitives.NotRule.apply
private abbrev validRule (addressWidth : Nat) :=
  occurrence addressWidth .validInverter Primitives.NotRule.apply
private abbrev readRule (addressWidth : Nat) :=
  occurrence addressWidth .readGate Primitives.AndRule.apply
private abbrev writeRule (addressWidth : Nat) :=
  occurrence addressWidth .writeGate Primitives.AndRule.apply

private theorem readSplitWrites (addressWidth : Nat)
    (index : Fin (addressWidth + 1)) :
    index ∈ (readSplitRule addressWidth).writes := by
  change index ∈ (pointerSplitter addressWidth).ports.outputs.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq
    ((pointerSplitter addressWidth).ports.outputs.labels.locate index) ▸
      List.get_mem _ _

private theorem writeSplitWrites (addressWidth : Nat)
    (index : Fin (addressWidth + 1)) :
    index ∈ (writeSplitRule addressWidth).writes := by
  change index ∈ (pointerSplitter addressWidth).ports.outputs.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq
    ((pointerSplitter addressWidth).ports.outputs.labels.locate index) ▸
      List.get_mem _ _

@[simp] private theorem componentWrites (addressWidth : Nat) :
    (readAddressRule addressWidth).writes = [.value] := rfl
@[simp] private theorem componentWrites' (addressWidth : Nat) :
    (writeAddressRule addressWidth).writes = [.value] := rfl
@[simp] private theorem addressEqualityWrites (addressWidth : Nat) :
    (addressEqualityRule addressWidth).writes = [.result] := rfl
@[simp] private theorem wrapEqualityWrites (addressWidth : Nat) :
    (wrapEqualityRule addressWidth).writes = [.output] := rfl
@[simp] private theorem wrapDifferenceWrites (addressWidth : Nat) :
    (wrapDifferenceRule addressWidth).writes = [.output] := rfl
@[simp] private theorem emptyWrites (addressWidth : Nat) :
    (emptyRule addressWidth).writes = [.output] := rfl
@[simp] private theorem fullWrites (addressWidth : Nat) :
    (fullRule addressWidth).writes = [.output] := rfl
@[simp] private theorem readyWrites (addressWidth : Nat) :
    (readyRule addressWidth).writes = [.output] := rfl
@[simp] private theorem validWrites (addressWidth : Nat) :
    (validRule addressWidth).writes = [.output] := rfl
@[simp] private theorem readWrites (addressWidth : Nat) :
    (readRule addressWidth).writes = [.output] := rfl
@[simp] private theorem writeWrites (addressWidth : Nat) :
    (writeRule addressWidth).writes = [.output] := rfl

private def outputSchedule (addressWidth : Nat) :
    Certified.OutputSchedule (body addressWidth) (children addressWidth)
      (cycleContract addressWidth) .apply :=
  .call (readSplitRule addressWidth)
    (by intro input _; cases input; simp [cycleContract, outputRule,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
      Certified.sourceAvailable, body, wiring, context,
      EndpointContext.moduleInput])
    (by simp)
  (.call (writeSplitRule addressWidth)
    (by intro input _; cases input; simp [cycleContract, outputRule,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
      Certified.sourceAvailable, body, wiring, context,
      EndpointContext.moduleInput])
    (by simp)
  (.call (readAddressRule addressWidth)
    (by intro index _; exact ⟨SignalComponentRule.apply, by simp,
      readSplitWrites addressWidth index.castSucc⟩)
    (by simp)
  (.call (writeAddressRule addressWidth)
    (by intro index _; exact ⟨SignalComponentRule.apply, by simp,
      writeSplitWrites addressWidth index.castSucc⟩)
    (by simp)
  (.call (addressEqualityRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨SignalComponentRule.apply, by simp, by simp⟩
      | right => exact ⟨SignalComponentRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (wrapEqualityRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨SignalComponentRule.apply, by simp,
          readSplitWrites addressWidth (Fin.last addressWidth)⟩
      | right => exact ⟨SignalComponentRule.apply, by simp,
          writeSplitWrites addressWidth (Fin.last addressWidth)⟩)
    (by simp)
  (.call (wrapDifferenceRule addressWidth)
    (by intro port _; cases port
        exact ⟨Primitives.EqRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (emptyRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨Equality.Rule.apply, by simp, by simp⟩
      | right => exact ⟨Primitives.EqRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (fullRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨Equality.Rule.apply, by simp, by simp⟩
      | right => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (readyRule addressWidth)
    (by intro port _; cases port
        exact ⟨Primitives.AndRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (validRule addressWidth)
    (by intro port _; cases port
        exact ⟨Primitives.AndRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (readRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
      | right => simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (writeRule addressWidth)
    (by
      intro input _
      cases input with
      | left => simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput]
      | right => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output with
    | readAddress => exact ⟨SignalComponentRule.apply, by simp, by simp⟩
    | writeAddress => exact ⟨SignalComponentRule.apply, by simp, by simp⟩
    | inputReady => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
    | outputValid => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
    | readAdvance => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩
    | writeAdvance => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩))))))))))))))

private def stateSchedule (addressWidth : Nat) :
    Certified.StateSchedule (body addressWidth) (children addressWidth) :=
  .done (by
    intro child input member
    cases child with
    | readSplit | writeSplit | readAddress | writeAddress =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | addressEquality =>
        rw [Equality.certified_cycleContract] at member
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | wrapEquality | wrapDifference | emptyGate | fullGate |
        readyInverter | validInverter | readGate | writeGate =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member)

private def ruleSchedules (addressWidth : Nat) :
    Certified.RuleSchedules (body addressWidth) (children addressWidth)
      (cycleContract addressWidth) where
  output | .apply => outputSchedule addressWidth
  state := stateSchedule addressWidth

private theorem coversChildren (addressWidth : Nat) :
    (ruleSchedules addressWidth).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (ruleSchedules addressWidth) .apply
  cases child <;> cases rule <;>
    simp [ruleSchedules, outputSchedule, Certified.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (addressWidth : Nat) :
    (Certified.moduleStructure (body addressWidth)
      (children addressWidth)).HasAtMostOneSolution :=
  (ruleSchedules addressWidth).hasAtMostOneSolution
    (coversChildren addressWidth)

private def splitInputs (addressWidth : Nat) (pointer : Pointer addressWidth) :
    (pointerSplitter addressWidth).ports.inputs.Values
  | .value => pointer

private noncomputable def addressInputs (addressWidth : Nat)
    (split : ProposedValues
      (children addressWidth .readSplit).moduleStructure) :
    (addressCombiner addressWidth).ports.inputs.Values :=
  fun index => split.outputs index.castSucc

private noncomputable def equalityInputs (addressWidth : Nat)
    (readAddress : ProposedValues
      (children addressWidth .readAddress).moduleStructure)
    (writeAddress : ProposedValues
      (children addressWidth .writeAddress).moduleStructure) :
    (Equality.ports (addressType addressWidth)).inputs.Values
  | .left => readAddress.outputs .value
  | .right => writeAddress.outputs .value

private noncomputable def wrapInputs (addressWidth : Nat)
    (readSplit : ProposedValues
      (children addressWidth .readSplit).moduleStructure)
    (writeSplit : ProposedValues
      (children addressWidth .writeSplit).moduleStructure) :
    Primitives.eq.ports.inputs.Values
  | .left => readSplit.outputs (Fin.last addressWidth)
  | .right => writeSplit.outputs (Fin.last addressWidth)

private def unaryInputs (value : Bool) : Primitives.not.ports.inputs.Values
  | .input => value

private def binaryInputs (left right : Bool) : Primitives.and.ports.inputs.Values
  | .left => left
  | .right => right

private theorem hasStructuralResult (addressWidth : Nat)
    (inputs : (ports addressWidth).inputs.Values)
    (currentState : (Certified.moduleStructure (body addressWidth)
      (children addressWidth)).State) :
    ∃ proposal, (Certified.moduleStructure (body addressWidth)
      (children addressWidth)).IsSolution inputs currentState proposal := by
  rcases (children addressWidth .readSplit).hasStructuralResult
      (splitInputs addressWidth (inputs .readPointer))
      (currentState .readSplit) with ⟨readSplit, readSplitSatisfies⟩
  rcases (children addressWidth .writeSplit).hasStructuralResult
      (splitInputs addressWidth (inputs .writePointer))
      (currentState .writeSplit) with ⟨writeSplit, writeSplitSatisfies⟩
  rcases (children addressWidth .readAddress).hasStructuralResult
      (addressInputs addressWidth readSplit) (currentState .readAddress) with
    ⟨readAddress, readAddressSatisfies⟩
  rcases (children addressWidth .writeAddress).hasStructuralResult
      (addressInputs addressWidth writeSplit) (currentState .writeAddress) with
    ⟨writeAddress, writeAddressSatisfies⟩
  rcases (children addressWidth .addressEquality).hasStructuralResult
      (equalityInputs addressWidth readAddress writeAddress)
      (currentState .addressEquality) with
    ⟨addressEquality, addressEqualitySatisfies⟩
  rcases (children addressWidth .wrapEquality).hasStructuralResult
      (wrapInputs addressWidth readSplit writeSplit)
      (currentState .wrapEquality) with ⟨wrapEquality, wrapEqualitySatisfies⟩
  rcases (children addressWidth .wrapDifference).hasStructuralResult
      (unaryInputs (wrapEquality.outputs .output))
      (currentState .wrapDifference) with
    ⟨wrapDifference, wrapDifferenceSatisfies⟩
  rcases (children addressWidth .emptyGate).hasStructuralResult
      (binaryInputs (addressEquality.outputs .result)
        (wrapEquality.outputs .output)) (currentState .emptyGate) with
    ⟨emptyGate, emptyGateSatisfies⟩
  rcases (children addressWidth .fullGate).hasStructuralResult
      (binaryInputs (addressEquality.outputs .result)
        (wrapDifference.outputs .output)) (currentState .fullGate) with
    ⟨fullGate, fullGateSatisfies⟩
  rcases (children addressWidth .readyInverter).hasStructuralResult
      (unaryInputs (fullGate.outputs .output))
      (currentState .readyInverter) with ⟨ready, readySatisfies⟩
  rcases (children addressWidth .validInverter).hasStructuralResult
      (unaryInputs (emptyGate.outputs .output))
      (currentState .validInverter) with ⟨valid, validSatisfies⟩
  rcases (children addressWidth .readGate).hasStructuralResult
      (binaryInputs (valid.outputs .output) (inputs .outputReady))
      (currentState .readGate) with ⟨readGate, readGateSatisfies⟩
  rcases (children addressWidth .writeGate).hasStructuralResult
      (binaryInputs (inputs .inputValid) (ready.outputs .output))
      (currentState .writeGate) with ⟨writeGate, writeGateSatisfies⟩
  let proposals : (child : Instance) →
      ProposedValues (childStructure addressWidth child)
    | .readSplit => readSplit
    | .writeSplit => writeSplit
    | .readAddress => readAddress
    | .writeAddress => writeAddress
    | .addressEquality => addressEquality
    | .wrapEquality => wrapEquality
    | .wrapDifference => wrapDifference
    | .emptyGate => emptyGate
    | .fullGate => fullGate
    | .readyInverter => ready
    | .validInverter => valid
    | .readGate => readGate
    | .writeGate => writeGate
  let outputs : (ports addressWidth).outputs.Values := fun
    | .readAddress => readAddress.outputs .value
    | .writeAddress => writeAddress.outputs .value
    | .inputReady => ready.outputs .output
    | .outputValid => valid.outputs .output
    | .readAdvance => readGate.outputs .output
    | .writeAdvance => writeGate.outputs .output
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | readSplit =>
        change (children addressWidth .readSplit).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .readSplit)
          (currentState .readSplit) readSplit
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readSplit =
            splitInputs addressWidth (inputs .readPointer) by
          funext port; cases port; rfl]
        exact readSplitSatisfies
    | writeSplit =>
        change (children addressWidth .writeSplit).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .writeSplit)
          (currentState .writeSplit) writeSplit
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .writeSplit =
            splitInputs addressWidth (inputs .writePointer) by
          funext port; cases port; rfl]
        exact writeSplitSatisfies
    | readAddress =>
        change (children addressWidth .readAddress).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .readAddress)
          (currentState .readAddress) readAddress
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readAddress =
            addressInputs addressWidth readSplit by funext index; rfl]
        exact readAddressSatisfies
    | writeAddress =>
        change (children addressWidth .writeAddress).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .writeAddress)
          (currentState .writeAddress) writeAddress
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .writeAddress =
            addressInputs addressWidth writeSplit by funext index; rfl]
        exact writeAddressSatisfies
    | addressEquality =>
        change (children addressWidth .addressEquality).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .addressEquality)
          (currentState .addressEquality) addressEquality
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .addressEquality =
            equalityInputs addressWidth readAddress writeAddress by
          funext port; cases port <;> rfl]
        exact addressEqualitySatisfies
    | wrapEquality =>
        change (children addressWidth .wrapEquality).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .wrapEquality)
          (currentState .wrapEquality) wrapEquality
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .wrapEquality =
            wrapInputs addressWidth readSplit writeSplit by
          funext port; cases port <;> rfl]
        exact wrapEqualitySatisfies
    | wrapDifference =>
        change (children addressWidth .wrapDifference).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .wrapDifference)
          (currentState .wrapDifference) wrapDifference
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .wrapDifference =
            unaryInputs (wrapEquality.outputs .output) by
          funext port; cases port; rfl]
        exact wrapDifferenceSatisfies
    | emptyGate =>
        change (children addressWidth .emptyGate).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .emptyGate)
          (currentState .emptyGate) emptyGate
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .emptyGate =
            binaryInputs (addressEquality.outputs .result)
              (wrapEquality.outputs .output) by funext port; cases port <;> rfl]
        exact emptyGateSatisfies
    | fullGate =>
        change (children addressWidth .fullGate).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .fullGate)
          (currentState .fullGate) fullGate
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .fullGate =
            binaryInputs (addressEquality.outputs .result)
              (wrapDifference.outputs .output) by funext port; cases port <;> rfl]
        exact fullGateSatisfies
    | readyInverter =>
        change (children addressWidth .readyInverter).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .readyInverter)
          (currentState .readyInverter) ready
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readyInverter =
            unaryInputs (fullGate.outputs .output) by funext port; cases port; rfl]
        exact readySatisfies
    | validInverter =>
        change (children addressWidth .validInverter).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .validInverter)
          (currentState .validInverter) valid
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .validInverter =
            unaryInputs (emptyGate.outputs .output) by funext port; cases port; rfl]
        exact validSatisfies
    | readGate =>
        change (children addressWidth .readGate).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .readGate)
          (currentState .readGate) readGate
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readGate =
            binaryInputs (valid.outputs .output) (inputs .outputReady) by
          funext port; cases port <;> rfl]
        exact readGateSatisfies
    | writeGate =>
        change (children addressWidth .writeGate).moduleStructure.IsSolution
          (ProposedValues.childInputs (body addressWidth)
            (childStructure addressWidth) inputs proposals .writeGate)
          (currentState .writeGate) writeGate
        rw [show ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .writeGate =
            binaryInputs (inputs .inputValid) (ready.outputs .output) by
          funext port; cases port <;> rfl]
        exact writeGateSatisfies

private def stateCorresponds (_ : (cycleContract addressWidth).state.Values)
    (_ : (Certified.moduleStructure (body addressWidth)
      (children addressWidth)).State) : Prop := True

private theorem implements (addressWidth : Nat) :
    Implements (Certified.moduleStructure (body addressWidth)
      (children addressWidth)) (cycleContract addressWidth)
      (stateCorresponds (addressWidth := addressWidth)) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have readSplitOutputs : (proposals .readSplit).outputs =
      (pointerSplitter addressWidth).outputValues
        (ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readSplit) :=
    childSatisfies .readSplit
  have writeSplitOutputs : (proposals .writeSplit).outputs =
      (pointerSplitter addressWidth).outputValues
        (ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .writeSplit) :=
    childSatisfies .writeSplit
  have readAddressOutputs : (proposals .readAddress).outputs =
      (addressCombiner addressWidth).outputValues
        (ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .readAddress) :=
    childSatisfies .readAddress
  have writeAddressOutputs : (proposals .writeAddress).outputs =
      (addressCombiner addressWidth).outputValues
        (ProposedValues.childInputs (body addressWidth)
          (childStructure addressWidth) inputs proposals .writeAddress) :=
    childSatisfies .writeAddress
  have readAddressValue : (proposals .readAddress).outputs .value =
      pointerAddress (inputs .readPointer) := by
    rw [congrFun readAddressOutputs .value]
    funext index
    change (proposals .readSplit).outputs index.castSucc =
      inputs .readPointer index.castSucc
    rw [congrFun readSplitOutputs index.castSucc]
    rfl
  have writeAddressValue : (proposals .writeAddress).outputs .value =
      pointerAddress (inputs .writePointer) := by
    rw [congrFun writeAddressOutputs .value]
    funext index
    change (proposals .writeSplit).outputs index.castSucc =
      inputs .writePointer index.castSucc
    rw [congrFun writeSplitOutputs index.castSucc]
    rfl
  rcases (children addressWidth .addressEquality).hasCorrespondingState
      (structuralState .addressEquality) with
    ⟨addressEqualityState, addressEqualityCorresponds⟩
  have addressEqualityState_eq : addressEqualityState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst addressEqualityState
  have addressEqualityMatches := Certified.childSolutionMatchesContract
    (children addressWidth) inputs structuralState (outputs, proposals)
      ⟨boundary, childSatisfies⟩ .addressEquality SignalMap.emptyValues
      addressEqualityCorresponds
  rcases addressEqualityMatches with ⟨addressEqualityEvaluates, _⟩
  have addressEqualityOutput :=
    (Equality.outputRule_holds_iff (addressType addressWidth) _ _ _).mp
      (addressEqualityEvaluates.1 Equality.Rule.apply)
  change (proposals .addressEquality).outputs .result =
    (addressType addressWidth).equal
      ((proposals .readAddress).outputs .value)
      ((proposals .writeAddress).outputs .value) at addressEqualityOutput
  have addressEqualityValue : (proposals .addressEquality).outputs .result =
      addressesEqual (inputs .readPointer) (inputs .writePointer) := by
    rw [addressEqualityOutput, readAddressValue, writeAddressValue]
    rfl
  have wrapEqualitySolution := childSatisfies .wrapEquality
  change Primitives.eq.IsSolution _ _ _ _ at wrapEqualitySolution
  have wrapEqualityOutput := congrFun wrapEqualitySolution.1 .output
  change (proposals .wrapEquality).outputs .output =
    SignalType.bit.equal
      ((proposals .readSplit).outputs (Fin.last addressWidth))
      ((proposals .writeSplit).outputs (Fin.last addressWidth)) at wrapEqualityOutput
  have wrapEqualityValue : (proposals .wrapEquality).outputs .output =
      wrapsEqual (inputs .readPointer) (inputs .writePointer) := by
    rw [wrapEqualityOutput,
      congrFun readSplitOutputs (Fin.last addressWidth),
      congrFun writeSplitOutputs (Fin.last addressWidth)]
    rfl
  have wrapDifferenceSolution := childSatisfies .wrapDifference
  change Primitives.not.IsSolution _ _ _ _ at wrapDifferenceSolution
  have wrapDifferenceOutput := congrFun wrapDifferenceSolution.1 .output
  change (proposals .wrapDifference).outputs .output =
    !(proposals .wrapEquality).outputs .output at wrapDifferenceOutput
  have wrapDifferenceValue : (proposals .wrapDifference).outputs .output =
      wrapsDiffer (inputs .readPointer) (inputs .writePointer) := by
    rw [wrapDifferenceOutput, wrapEqualityValue]
    rfl
  have emptySolution := childSatisfies .emptyGate
  change Primitives.and.IsSolution _ _ _ _ at emptySolution
  have emptyOutput := congrFun emptySolution.1 .output
  change (proposals .emptyGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapEquality).outputs .output) at emptyOutput
  have emptyValue : (proposals .emptyGate).outputs .output =
      empty (inputs .readPointer) (inputs .writePointer) := by
    rw [emptyOutput, addressEqualityValue, wrapEqualityValue]
    rfl
  have fullSolution := childSatisfies .fullGate
  change Primitives.and.IsSolution _ _ _ _ at fullSolution
  have fullOutput := congrFun fullSolution.1 .output
  change (proposals .fullGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapDifference).outputs .output) at fullOutput
  have fullValue : (proposals .fullGate).outputs .output =
      full (inputs .readPointer) (inputs .writePointer) := by
    rw [fullOutput, addressEqualityValue, wrapDifferenceValue]
    rfl
  have readySolution := childSatisfies .readyInverter
  change Primitives.not.IsSolution _ _ _ _ at readySolution
  have readyOutput := congrFun readySolution.1 .output
  change (proposals .readyInverter).outputs .output =
    !(proposals .fullGate).outputs .output at readyOutput
  have readyValue : (proposals .readyInverter).outputs .output =
      inputReady (inputs .readPointer) (inputs .writePointer) := by
    rw [readyOutput, fullValue]
    rfl
  have validSolution := childSatisfies .validInverter
  change Primitives.not.IsSolution _ _ _ _ at validSolution
  have validOutput := congrFun validSolution.1 .output
  change (proposals .validInverter).outputs .output =
    !(proposals .emptyGate).outputs .output at validOutput
  have validValue : (proposals .validInverter).outputs .output =
      outputValid (inputs .readPointer) (inputs .writePointer) := by
    rw [validOutput, emptyValue]
    rfl
  have readSolution := childSatisfies .readGate
  change Primitives.and.IsSolution _ _ _ _ at readSolution
  have readOutput := congrFun readSolution.1 .output
  change (proposals .readGate).outputs .output =
    ((proposals .validInverter).outputs .output && inputs .outputReady) at readOutput
  have readValue : (proposals .readGate).outputs .output =
      readAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .outputReady) := by
    rw [readOutput, validValue]
    rfl
  have writeSolution := childSatisfies .writeGate
  change Primitives.and.IsSolution _ _ _ _ at writeSolution
  have writeOutput := congrFun writeSolution.1 .output
  change (proposals .writeGate).outputs .output =
    (inputs .inputValid && (proposals .readyInverter).outputs .output) at writeOutput
  have writeValue : (proposals .writeGate).outputs .output =
      writeAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .inputValid) := by
    rw [writeOutput, readyValue]
    rfl
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (outputRule addressWidth).Holds inputs contractState outputs
    rw [outputRule_holds_iff]
    exact ⟨(boundary .readAddress).trans readAddressValue,
      (boundary .writeAddress).trans writeAddressValue,
      (boundary .inputReady).trans readyValue,
      (boundary .outputValid).trans validValue,
      (boundary .readAdvance).trans readValue,
      (boundary .writeAdvance).trans writeValue⟩
  · rfl

private noncomputable def proofCertification (addressWidth : Nat) :
    ModuleCycleCertification
      (Certified.moduleStructure (body addressWidth) (children addressWidth))
      (cycleContract addressWidth) where
  stateCorresponds := stateCorresponds (addressWidth := addressWidth)
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := hasStructuralResult addressWidth
  structuralResultUnique := hasAtMostOneSolution addressWidth
  implements := implements addressWidth

private noncomputable opaque certification (addressWidth : Nat) :
    ModuleCycleCertification (moduleStructure addressWidth)
      (cycleContract addressWidth) :=
  (proofCertification addressWidth).transportStructure
    (moduleStructure_eq addressWidth).symm

noncomputable def certified (addressWidth : Nat) :
    ModuleCycleCertified (ports addressWidth) :=
  (certification addressWidth).bundle

@[simp] theorem certified_moduleStructure (addressWidth : Nat) :
    (certified addressWidth).moduleStructure = moduleStructure addressWidth := rfl

@[simp] theorem certified_cycleContract (addressWidth : Nat) :
    (certified addressWidth).cycleContract = cycleContract addressWidth := rfl

end Silean2.Modules.FifoPointerControl

namespace Silean2.Modules.FifoPointerControl.Naming

open Silean2 Silean2.Naming

def ports (addressWidth : Nat) :
    ModulePortsNaming (Modules.FifoPointerControl.ports addressWidth) where
  inputs := ⟨fun
    | .readPointer => "read_pointer"
    | .writePointer => "write_pointer"
    | .inputValid => "input_valid"
    | .outputReady => "output_ready"⟩
  outputs := ⟨fun
    | .readAddress => "read_address"
    | .writeAddress => "write_address"
    | .inputReady => "input_ready"
    | .outputValid => "output_valid"
    | .readAdvance => "read_advance"
    | .writeAdvance => "write_advance"⟩
  inputTypes := fun
    | .readPointer | .writePointer => .vector .bit
    | .inputValid | .outputReady => .bit
  outputTypes := fun
    | .readAddress | .writeAddress => .vector .bit
    | .inputReady | .outputValid | .readAdvance | .writeAdvance => .bit

def naming (addressWidth : Nat) :
    ModuleNaming (Modules.FifoPointerControl.moduleStructure addressWidth) := by
  unfold Modules.FifoPointerControl.moduleStructure
  exact .composite
    ⟨"fifo_pointer_control", "structural", [.natural addressWidth]⟩
    (ports addressWidth)
    (fun
      | .readSplit => "read_split"
      | .writeSplit => "write_split"
      | .readAddress => "read_address_combiner"
      | .writeAddress => "write_address_combiner"
      | .addressEquality => "address_equality"
      | .wrapEquality => "wrap_equality"
      | .wrapDifference => "wrap_difference"
      | .emptyGate => "empty_gate"
      | .fullGate => "full_gate"
      | .readyInverter => "ready_inverter"
      | .validInverter => "valid_inverter"
      | .readGate => "read_gate"
      | .writeGate => "write_gate")
    (fun
      | .readSplit | .writeSplit => Silean2.Naming.SignalAdapter.splitter
          (Modules.FifoPointerControl.pointerSplitter addressWidth)
      | .readAddress | .writeAddress => Silean2.Naming.SignalAdapter.combiner
          (Modules.FifoPointerControl.addressCombiner addressWidth)
      | .addressEquality => Equality.Naming.naming
          (Modules.FifoPointerControl.addressType addressWidth)
      | .wrapEquality => Silean2.Naming.Primitive.eq
      | .wrapDifference | .readyInverter | .validInverter =>
          Silean2.Naming.Primitive.not
      | .emptyGate | .fullGate | .readGate | .writeGate =>
          Silean2.Naming.Primitive.and)

end Silean2.Modules.FifoPointerControl.Naming
