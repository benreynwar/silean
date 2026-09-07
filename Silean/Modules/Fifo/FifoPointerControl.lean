import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.Equality.Equality
import Silean.Primitives
import Silean.Composition.SignalAdapterImplementation
import Silean.Composition.SignalLogic

namespace Silean.Modules.Fifo.PointerControl

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

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

module_ports ports (addressWidth : Nat) where
  input readPointer : pointerType addressWidth,
  input writePointer : pointerType addressWidth,
  input inputValid : .bit,
  input outputReady : .bit,
  output readAddress : addressType addressWidth,
  output writeAddress : addressType addressWidth,
  output inputReady : .bit,
  output outputValid : .bit,
  output readAdvance : .bit,
  output writeAdvance : .bit

module_cycle_contract cycleContract (addressWidth : Nat) for ports addressWidth where
  state := emptySignalMap
  -- These outputs are separate rules because their FIFO parent consumes them
  -- at different scheduling boundaries. This prevents a forward-path request
  -- from acquiring the handshake inputs needed only by the state transition.
  output_rule readAddress where
    reads := [readPointer]
    writes := { readAddress := pointerAddress readPointer }
  output_rule writeAddress where
    reads := [writePointer]
    writes := { writeAddress := pointerAddress writePointer }
  output_rule inputReady where
    reads := [readPointer, writePointer]
    writes := { inputReady := inputReady readPointer writePointer }
  output_rule outputValid where
    reads := [readPointer, writePointer]
    writes := { outputValid := outputValid readPointer writePointer }
  output_rule readAdvance where
    reads := [readPointer, writePointer, outputReady]
    writes := {
      readAdvance := readAdvance readPointer writePointer outputReady }
  output_rule writeAdvance where
    reads := [readPointer, writePointer, inputValid]
    writes := {
      writeAdvance := writeAdvance readPointer writePointer inputValid }
  state_rule := Contracts.Cycle.CycleStateRule.empty _

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

def pointerSplitter (addressWidth : Nat) : Composition.SignalSplitter :=
  .vector (addressWidth + 1) .bit

def addressCombiner (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector addressWidth .bit
end Silean.Modules.Fifo.PointerControl

namespace Silean.Modules.Fifo

open Silean
open Silean.Authoring

module_design PointerControl (addressWidth : Nat) where
  boundary (PointerControl.ports addressWidth)
    (naming := PointerControl.Naming.ports addressWidth)
  instances {
    -- Split each extended pointer into address and wrap bits.
    readSplit := Naming.SignalAdapter.splitterDesign
      (PointerControl.pointerSplitter addressWidth),
    writeSplit := Naming.SignalAdapter.splitterDesign
      (PointerControl.pointerSplitter addressWidth),
    -- Reassemble the low bits as storage addresses.
    readAddress (name := "readAddressCombiner") := Naming.SignalAdapter.combinerDesign
      (PointerControl.addressCombiner addressWidth),
    writeAddress (name := "writeAddressCombiner") := Naming.SignalAdapter.combinerDesign
      (PointerControl.addressCombiner addressWidth),
    -- Derive empty, full, ready, valid, and transfer conditions.
    addressEquality := Equality.design
      (PointerControl.addressType addressWidth),
    wrapEquality := Primitives.eqDesign,
    wrapDifference := Primitives.notDesign,
    emptyGate := Primitives.andDesign,
    fullGate := Primitives.andDesign,
    readyInverter := Primitives.notDesign,
    validInverter := Primitives.notDesign,
    readGate := Primitives.andDesign,
    writeGate := Primitives.andDesign }
  wiring {
    outputs {
      .readAddress := readAddress.value,
      .writeAddress := writeAddress.value,
      .inputReady := readyInverter.output,
      .outputValid := validInverter.output,
      .readAdvance := readGate.output,
      .writeAdvance := writeGate.output }
    instance (.readSplit) { .value := input.readPointer }
    instance (.writeSplit) { .value := input.writePointer }
    instance (.readAddress) { index := readSplit[index.castSucc] }
    instance (.writeAddress) { index := writeSplit[index.castSucc] }
    instance (.addressEquality) {
      .left := readAddress.value,
      .right := writeAddress.value }
    instance (.wrapEquality) {
      .left := readSplit[Fin.last addressWidth],
      .right := writeSplit[Fin.last addressWidth] }
    instance (.wrapDifference) { .input := wrapEquality.output }
    instance (.emptyGate) {
      .left := addressEquality.result,
      .right := wrapEquality.output }
    instance (.fullGate) {
      .left := addressEquality.result,
      .right := wrapDifference.output }
    instance (.readyInverter) { .input := fullGate.output }
    instance (.validInverter) { .input := emptyGate.output }
    instance (.readGate) {
      .left := validInverter.output,
      .right := input.outputReady }
    instance (.writeGate) {
      .left := input.inputValid,
      .right := readyInverter.output }
  }

end Silean.Modules.Fifo
