import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Naming.ModuleNaming
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.Equality
import Silean.Primitives
import Silean.Composition.SignalAdapterImplementation
import Silean.Composition.SignalLogic

namespace Silean.Modules.Fifo.PointerControl

open Silean

/-! Combinational control for a FIFO built from a power-of-two register bank.
It derives storage addresses, empty/full status, valid/ready signals, and
pointer advances from extended read and write pointers. -/

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
    Contracts.Cycle.CycleOutputRule (ports addressWidth) emptySignalMap
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
    Contracts.Cycle.ModuleCycleContract (ports addressWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule addressWidth⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
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
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
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

private def pointerSplitter (addressWidth : Nat) : Composition.SignalSplitter :=
  .vector (addressWidth + 1) .bit

private def addressCombiner (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector addressWidth .bit

/-! ## Hardware structure -/

private inductive Instance
  /-- Splits the read pointer into address and wrap bits. -/
  | readSplit
  /-- Splits the write pointer into address and wrap bits. -/
  | writeSplit
  /-- Recombines the read-pointer address bits. -/
  | readAddress
  /-- Recombines the write-pointer address bits. -/
  | writeAddress
  /-- Tests whether the two entry addresses are equal. -/
  | addressEquality
  /-- Tests whether the two wrap bits are equal. -/
  | wrapEquality
  /-- Tests whether the two wrap bits differ. -/
  | wrapDifference
  /-- Detects equal addresses with equal wrap bits: the empty condition. -/
  | emptyGate
  /-- Detects equal addresses with different wrap bits: the full condition. -/
  | fullGate
  /-- Converts `full` into upstream readiness. -/
  | readyInverter
  /-- Converts `empty` into downstream validity. -/
  | validInverter
  /-- Advances reads when valid data is accepted. -/
  | readGate
  /-- Advances writes when incoming data is accepted. -/
  | writeGate
deriving Enumeration

@[reducible] private def instancePorts (addressWidth : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .readSplit | .writeSplit => (pointerSplitter addressWidth).ports
    | .readAddress | .writeAddress => (addressCombiner addressWidth).ports
    | .addressEquality => Equality.ports (addressType addressWidth)
    | .wrapEquality => Primitives.eq.ports
    | .wrapDifference | .readyInverter | .validInverter => Primitives.not.ports
    | .emptyGate | .fullGate | .readGate | .writeGate => Primitives.and.ports

@[reducible] private def context (addressWidth : Nat) : EndpointContext where
  ports := ports addressWidth
  instancePorts := instancePorts addressWidth

private def wiring (addressWidth : Nat) :
    Wiring (context addressWidth).ports (context addressWidth).instancePorts :=
  let c := context addressWidth
  { moduleOutput := fun
    -- Expose the reconstructed addresses and handshake decisions.
    | .readAddress => c.instanceOutput .readAddress .value
    | .writeAddress => c.instanceOutput .writeAddress .value
    | .inputReady => c.instanceOutput .readyInverter .output
    | .outputValid => c.instanceOutput .validInverter .output
    | .readAdvance => c.instanceOutput .readGate .output
    | .writeAdvance => c.instanceOutput .writeGate .output
    instanceInput := fun
    -- Split both extended pointers into address bits and a wrap bit.
    | .readSplit, .value => c.moduleInput .readPointer
    | .writeSplit, .value => c.moduleInput .writePointer
    -- Recombine the low bits as storage addresses.
    | .readAddress, index =>
        c.instanceOutput .readSplit index.castSucc
    | .writeAddress, index =>
        c.instanceOutput .writeSplit index.castSucc
    -- Compare addresses and wrap bits independently.
    | .addressEquality, .left =>
        c.instanceOutput .readAddress .value
    | .addressEquality, .right =>
        c.instanceOutput .writeAddress .value
    | .wrapEquality, .left =>
        c.instanceOutput .readSplit (Fin.last addressWidth)
    | .wrapEquality, .right =>
        c.instanceOutput .writeSplit (Fin.last addressWidth)
    | .wrapDifference, .input =>
        c.instanceOutput .wrapEquality .output
    -- Equal addresses mean empty or full depending on the wrap bits.
    | .emptyGate, .left =>
        c.instanceOutput .addressEquality .result
    | .emptyGate, .right =>
        c.instanceOutput .wrapEquality .output
    | .fullGate, .left =>
        c.instanceOutput .addressEquality .result
    | .fullGate, .right =>
        c.instanceOutput .wrapDifference .output
    -- Ready is not-full and valid is not-empty.
    | .readyInverter, .input =>
        c.instanceOutput .fullGate .output
    | .validInverter, .input =>
        c.instanceOutput .emptyGate .output
    -- Advance a pointer only when its valid/ready transfer occurs.
    | .readGate, .left =>
        c.instanceOutput .validInverter .output
    | .readGate, .right => c.moduleInput .outputReady
    | .writeGate, .left => c.moduleInput .inputValid
    | .writeGate, .right =>
        c.instanceOutput .readyInverter .output }

@[reducible] private def body (addressWidth : Nat) : ModuleBody :=
  ⟨context addressWidth, wiring addressWidth⟩

@[reducible] private def structuralChildren (addressWidth : Nat) :
    (name : (instancePorts addressWidth).Name) →
      ModuleStructure ((instancePorts addressWidth).ports name)
  | .readSplit | .writeSplit => .splitter (pointerSplitter addressWidth)
  | .readAddress | .writeAddress => .combiner (addressCombiner addressWidth)
  | .addressEquality => Equality.moduleStructure (addressType addressWidth)
  | .wrapEquality => .primitive Primitives.eq
  | .wrapDifference | .readyInverter | .validInverter => .primitive Primitives.not
  | .emptyGate | .fullGate | .readGate | .writeGate => .primitive Primitives.and

def moduleStructure (addressWidth : Nat) : ModuleStructure (ports addressWidth) :=
  .composite (body addressWidth) (structuralChildren addressWidth)

@[reducible] private def childContracts (addressWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (body addressWidth)
  | .readSplit | .writeSplit => (pointerSplitter addressWidth).cycleContract
  | .readAddress | .writeAddress => (addressCombiner addressWidth).cycleContract
  | .addressEquality => Equality.cycleContract (addressType addressWidth)
  | .wrapEquality => Primitives.eqCycleContract
  | .wrapDifference | .readyInverter | .validInverter => Primitives.notCycleContract
  | .emptyGate | .fullGate | .readGate | .writeGate => Primitives.andCycleContract

private abbrev occurrence (addressWidth : Nat) (child : Instance)
    (rule : (childContracts addressWidth child).RuleName) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body addressWidth) (childContracts addressWidth) := ⟨child, rule⟩

private abbrev readSplitRule (addressWidth : Nat) :=
  occurrence addressWidth .readSplit Composition.SignalComponentRule.apply
private abbrev writeSplitRule (addressWidth : Nat) :=
  occurrence addressWidth .writeSplit Composition.SignalComponentRule.apply
private abbrev readAddressRule (addressWidth : Nat) :=
  occurrence addressWidth .readAddress Composition.SignalComponentRule.apply
private abbrev writeAddressRule (addressWidth : Nat) :=
  occurrence addressWidth .writeAddress Composition.SignalComponentRule.apply
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
    Contracts.Cycle.Certification.Layer.OutputSchedule
      (body addressWidth) (childContracts addressWidth)
      (cycleContract addressWidth) .apply :=
  .call (readSplitRule addressWidth)
    (by intro input _; cases input; simp [cycleContract, outputRule,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
      Contracts.Cycle.Certification.Layer.sourceAvailable, body, wiring, context,
      EndpointContext.moduleInput])
    (by simp)
  (.call (writeSplitRule addressWidth)
    (by intro input _; cases input; simp [cycleContract, outputRule,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
      Contracts.Cycle.Certification.Layer.sourceAvailable, body, wiring, context,
      EndpointContext.moduleInput])
    (by simp)
  (.call (readAddressRule addressWidth)
    (by intro index _; exact ⟨Composition.SignalComponentRule.apply, by simp,
      readSplitWrites addressWidth index.castSucc⟩)
    (by simp)
  (.call (writeAddressRule addressWidth)
    (by intro index _; exact ⟨Composition.SignalComponentRule.apply, by simp,
      writeSplitWrites addressWidth index.castSucc⟩)
    (by simp)
  (.call (addressEqualityRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨Composition.SignalComponentRule.apply, by simp, by simp⟩
      | right => exact ⟨Composition.SignalComponentRule.apply, by simp, by simp⟩)
    (by simp)
  (.call (wrapEqualityRule addressWidth)
    (by
      intro input _
      cases input with
      | left => exact ⟨Composition.SignalComponentRule.apply, by simp,
          readSplitWrites addressWidth (Fin.last addressWidth)⟩
      | right => exact ⟨Composition.SignalComponentRule.apply, by simp,
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
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (writeRule addressWidth)
    (by
      intro input _
      cases input with
      | left => simp [cycleContract, outputRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.Layer.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput]
      | right => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output with
    | readAddress => exact ⟨Composition.SignalComponentRule.apply, by simp, by simp⟩
    | writeAddress => exact ⟨Composition.SignalComponentRule.apply, by simp, by simp⟩
    | inputReady => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
    | outputValid => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
    | readAdvance => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩
    | writeAdvance => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩))))))))))))))

private def stateSchedule (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (body addressWidth) (childContracts addressWidth) :=
  .done (by
    intro child input member
    cases child with
    | readSplit | writeSplit | readAddress | writeAddress =>
        change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | addressEquality =>
        simp [childContracts] at member
    | wrapEquality | wrapDifference | emptyGate | fullGate |
        readyInverter | validInverter | readGate | writeGate =>
        change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member)

private def ruleSchedules (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleSchedules
      (body addressWidth) (childContracts addressWidth)
      (cycleContract addressWidth) where
  output | .apply => outputSchedule addressWidth
  state := stateSchedule addressWidth

private theorem coversChildren (addressWidth : Nat) :
    (ruleSchedules addressWidth).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  cases child <;> cases rule <;>
    simp [ruleSchedules, outputSchedule,
      Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

section LayerCertification

variable (addressWidth : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body addressWidth) (childContracts addressWidth))

private def stateCorresponds (_ : (cycleContract addressWidth).state.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body addressWidth) layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body addressWidth) layerChildren)
      (cycleContract addressWidth)
      (stateCorresponds addressWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      (fun child => by cases child <;> exact SignalMap.emptyValues)
      (by intro child; cases child <;>
        change Subsingleton emptySignalMap.Values <;> infer_instance)
  rcases proposal with ⟨outputs, proposals⟩
  have boundary := satisfies.1
  have readSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .readSplit).1.1 Composition.SignalComponentRule.apply)
  have writeSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .writeSplit).1.1 Composition.SignalComponentRule.apply)
  have readAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .readAddress).1.1 Composition.SignalComponentRule.apply)
  have writeAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .writeAddress).1.1 Composition.SignalComponentRule.apply)
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
  have addressEqualityOutput :=
    (Equality.outputRule_holds_iff (addressType addressWidth) _ _ _).mp
      ((childMatches .addressEquality).1.1 Equality.Rule.apply)
  change (proposals .addressEquality).outputs .result =
    (addressType addressWidth).equal
      ((proposals .readAddress).outputs .value)
      ((proposals .writeAddress).outputs .value) at addressEqualityOutput
  have addressEqualityValue : (proposals .addressEquality).outputs .result =
      addressesEqual (inputs .readPointer) (inputs .writePointer) := by
    rw [addressEqualityOutput, readAddressValue, writeAddressValue]
    rfl
  have wrapEqualityOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapEquality).1.1 Primitives.EqRule.apply)
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
  have wrapDifferenceOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapDifference).1.1 Primitives.NotRule.apply)
  change (proposals .wrapDifference).outputs .output =
    !(proposals .wrapEquality).outputs .output at wrapDifferenceOutput
  have wrapDifferenceValue : (proposals .wrapDifference).outputs .output =
      wrapsDiffer (inputs .readPointer) (inputs .writePointer) := by
    rw [wrapDifferenceOutput, wrapEqualityValue]
    rfl
  have emptyOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .emptyGate).1.1 Primitives.AndRule.apply)
  change (proposals .emptyGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapEquality).outputs .output) at emptyOutput
  have emptyValue : (proposals .emptyGate).outputs .output =
      empty (inputs .readPointer) (inputs .writePointer) := by
    rw [emptyOutput, addressEqualityValue, wrapEqualityValue]
    rfl
  have fullOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .fullGate).1.1 Primitives.AndRule.apply)
  change (proposals .fullGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapDifference).outputs .output) at fullOutput
  have fullValue : (proposals .fullGate).outputs .output =
      full (inputs .readPointer) (inputs .writePointer) := by
    rw [fullOutput, addressEqualityValue, wrapDifferenceValue]
    rfl
  have readyOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .readyInverter).1.1 Primitives.NotRule.apply)
  change (proposals .readyInverter).outputs .output =
    !(proposals .fullGate).outputs .output at readyOutput
  have readyValue : (proposals .readyInverter).outputs .output =
      inputReady (inputs .readPointer) (inputs .writePointer) := by
    rw [readyOutput, fullValue]
    rfl
  have validOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .validInverter).1.1 Primitives.NotRule.apply)
  change (proposals .validInverter).outputs .output =
    !(proposals .emptyGate).outputs .output at validOutput
  have validValue : (proposals .validInverter).outputs .output =
      outputValid (inputs .readPointer) (inputs .writePointer) := by
    rw [validOutput, emptyValue]
    rfl
  have readOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .readGate).1.1 Primitives.AndRule.apply)
  change (proposals .readGate).outputs .output =
    ((proposals .validInverter).outputs .output && inputs .outputReady) at readOutput
  have readValue : (proposals .readGate).outputs .output =
      readAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .outputReady) := by
    rw [readOutput, validValue]
    rfl
  have writeOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .writeGate).1.1 Primitives.AndRule.apply)
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

end LayerCertification

/-- The pointer-control wiring implements its combinational contract for any
children satisfying the declared adapter, equality, and bit-logic contracts. -/
noncomputable opaque certifiedLayer (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body addressWidth) (childContracts addressWidth)
      (cycleContract addressWidth) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules addressWidth) (coversChildren addressWidth)
    (stateCorresponds addressWidth) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (implements addressWidth)

@[reducible] private noncomputable def certifiedChildren (addressWidth : Nat) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body addressWidth) (childContracts addressWidth)
  | .readSplit | .writeSplit => (pointerSplitter addressWidth).certified.certifiedStructure
  | .readAddress | .writeAddress => (addressCombiner addressWidth).certified.certifiedStructure
  | .addressEquality => (Equality.certified (addressType addressWidth)).certifiedStructure
  | .wrapEquality => Primitives.eqCertified.certifiedStructure
  | .wrapDifference | .readyInverter | .validInverter =>
      Primitives.notCertified.certifiedStructure
  | .emptyGate | .fullGate | .readGate | .writeGate =>
      Primitives.andCertified.certifiedStructure

private noncomputable opaque certification (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure addressWidth)
      (cycleContract addressWidth) :=
  (certifiedLayer addressWidth).certifyComposite
    (structuralChildren addressWidth) (certifiedChildren addressWidth) (by
      intro child
      cases child with
      | addressEquality => exact Equality.certified_moduleStructure (addressType addressWidth)
      | readSplit | writeSplit | readAddress | writeAddress |
          wrapEquality | wrapDifference | emptyGate | fullGate |
          readyInverter | validInverter | readGate | writeGate => rfl)

noncomputable def certified (addressWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports addressWidth) :=
  (certification addressWidth).bundle

@[simp] theorem certified_moduleStructure (addressWidth : Nat) :
    (certified addressWidth).moduleStructure = moduleStructure addressWidth := rfl

@[simp] theorem certified_cycleContract (addressWidth : Nat) :
    (certified addressWidth).cycleContract = cycleContract addressWidth := rfl

end Silean.Modules.Fifo.PointerControl

namespace Silean.Modules.Fifo.PointerControl.Naming

open Silean Silean.Naming

def ports (addressWidth : Nat) :
    ModulePortsNaming (Modules.Fifo.PointerControl.ports addressWidth) where
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
    ModuleNaming (Modules.Fifo.PointerControl.moduleStructure addressWidth) := by
  unfold Modules.Fifo.PointerControl.moduleStructure
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
      | .readSplit | .writeSplit => Silean.Naming.SignalAdapter.splitter
          (Modules.Fifo.PointerControl.pointerSplitter addressWidth)
      | .readAddress | .writeAddress => Silean.Naming.SignalAdapter.combiner
          (Modules.Fifo.PointerControl.addressCombiner addressWidth)
      | .addressEquality => Equality.Naming.naming
          (Modules.Fifo.PointerControl.addressType addressWidth)
      | .wrapEquality => Silean.Naming.Primitive.eq
      | .wrapDifference | .readyInverter | .validInverter =>
          Silean.Naming.Primitive.not
      | .emptyGate | .fullGate | .readGate | .writeGate =>
          Silean.Naming.Primitive.and)

end Silean.Modules.Fifo.PointerControl.Naming
