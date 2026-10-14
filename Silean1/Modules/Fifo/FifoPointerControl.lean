import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Authoring.CircuitLogic
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.Equality.Equality
import Silean.Primitives
import Silean.Composition.SignalAdapterImplementation
import Silean.Composition.SignalLogic

namespace Silean.Modules.Fifo.PointerControl

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

/-! Combinational control for a FIFO built from a power-of-two register bank.
It derives storage addresses, empty/full status, valid/ready signals, and
pointer advances from extended read and write pointers. -/

abbrev Pointer (addressWidth : Nat) := Fin (addressWidth + 1) → Bool
abbrev Address (addressWidth : Nat) := Fin addressWidth → Bool

@[reducible] def pointerType (addressWidth : Nat) : SignalType :=
  .vector (addressWidth + 1) .bit

@[reducible] def addressType (addressWidth : Nat) : SignalType :=
  .vector addressWidth .bit

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

open ports

def pointerSplitter (addressWidth : Nat) : Composition.SignalSplitter :=
  .vector (addressWidth + 1) .bit

def addressCombiner (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector addressWidth .bit

/-! ## Authored hardware -/

noncomputable def construction (addressWidth : Nat) :
    ModuleBuilder (ports addressWidth) Unit := do
  let readPointer ← input addressWidth .readPointer
  let writePointer ← input addressWidth .writePointer
  let inputValid ← input addressWidth .inputValid
  let outputReady ← input addressWidth .outputReady

  let readSplit ← split (pointerSplitter addressWidth) readPointer
  let writeSplit ← split (pointerSplitter addressWidth) writePointer
  let readAddress ← combine (addressCombiner addressWidth)
    (fun index => readSplit index.castSucc)
  let writeAddress ← combine (addressCombiner addressWidth)
    (fun index => writeSplit index.castSucc)
  let readWrap : Net .bit := readSplit (Fin.last addressWidth)
  let writeWrap : Net .bit := writeSplit (Fin.last addressWidth)

  wire addressesEqual ← readAddress === writeAddress
  wire wrapsEqual ← readWrap === writeWrap
  let inputReady ← !! (← addressesEqual &&& (← !! wrapsEqual))
  let outputValid ← !! (← addressesEqual &&& wrapsEqual)

  output addressWidth .readAddress readAddress
  output addressWidth .writeAddress writeAddress
  output addressWidth .inputReady inputReady
  output addressWidth .outputValid outputValid
  output addressWidth .readAdvance (← outputValid &&& outputReady)
  output addressWidth .writeAdvance (← inputValid &&& inputReady)

noncomputable def description (addressWidth : Nat) : Description :=
  ModuleBuilder.build (Naming.ports addressWidth) (construction addressWidth)

/-! ## Exact combinational behavior -/

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
    writes := {
      inputReady := PointerControl.inputReady readPointer writePointer }
  output_rule outputValid where
    reads := [readPointer, writePointer]
    writes := {
      outputValid := PointerControl.outputValid readPointer writePointer }
  output_rule readAdvance where
    reads := [readPointer, writePointer, outputReady]
    writes := {
      readAdvance :=
        PointerControl.readAdvance readPointer writePointer outputReady }
  output_rule writeAdvance where
    reads := [readPointer, writePointer, inputValid]
    writes := {
      writeAdvance :=
        PointerControl.writeAdvance readPointer writePointer inputValid }
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

end Silean.Modules.Fifo.PointerControl
