import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitLogic
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.Equality.Equality
import Silean.Primitives
import Silean.Composition.SignalAdapterImplementation
import Silean.Composition.SignalLogic
import Silean.Modules.Fifo.Internal.FifoPointerControlStructure

namespace Silean.Modules.Fifo.PointerControl

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-! Combinational control for a FIFO built from a power-of-two register bank.
It derives storage addresses, empty/full status, valid/ready signals, and
pointer advances from extended read and write pointers. -/

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

/-- The complete combinational behavior of the pointer controller. Keeping the
six equations together gives readers and parent proofs one semantic view,
while the contract retains separate rules for dependency scheduling. -/
structure Behavior (addressWidth : Nat)
    (inputs : (ports addressWidth).inputs.Values)
    (outputs : (ports addressWidth).outputs.Values) : Prop where
  readAddress : outputs .readAddress = pointerAddress (inputs .readPointer)
  writeAddress : outputs .writeAddress = pointerAddress (inputs .writePointer)
  inputReady : outputs .inputReady =
    inputReady (inputs .readPointer) (inputs .writePointer)
  outputValid : outputs .outputValid =
    outputValid (inputs .readPointer) (inputs .writePointer)
  readAdvance : outputs .readAdvance =
    readAdvance (inputs .readPointer) (inputs .writePointer)
      (inputs .outputReady)
  writeAdvance : outputs .writeAdvance =
    writeAdvance (inputs .readPointer) (inputs .writePointer)
      (inputs .inputValid)

namespace Behavior

/-- An allowed contract step satisfies every pointer-control equation. -/
theorem of_allowed (addressWidth : Nat) {step : (cycleContract addressWidth).Step}
    (allowed : (cycleContract addressWidth).Allows step) :
    Behavior addressWidth step.inputs step.outputs :=
  ⟨(readAddressRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .readAddress),
    (writeAddressRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .writeAddress),
    (inputReadyRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .inputReady),
    (outputValidRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .outputValid),
    (readAdvanceRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .readAdvance),
    (writeAdvanceRule_holds_iff addressWidth _ _ _).mp
      (allowed.1 .writeAdvance)⟩

end Behavior

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

/-! ## Authored hardware -/

namespace Description

open Authoring.CircuitDescription
open Authoring.CircuitLogic
open scoped Authoring.CircuitLogic

noncomputable def construction (addressWidth : Nat) : Builder Unit := do
  let readPointer ← input "readPointer" (pointerType addressWidth)
  let writePointer ← input "writePointer" (pointerType addressWidth)
  let inputValid ← input "inputValid" .bit
  let outputReady ← input "outputReady" .bit

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

  output "readAddress" readAddress
  output "writeAddress" writeAddress
  output "inputReady" inputReady
  output "outputValid" outputValid
  output "readAdvance" (← outputValid &&& outputReady)
  output "writeAdvance" (← inputValid &&& inputReady)

noncomputable def description (addressWidth : Nat) : Description :=
  build (construction addressWidth)

end Description

/-! ## Placement -/

open Authoring.CircuitDescription

/-- Outputs produced by a placed pointer controller. -/
structure PlacedOutputs (addressWidth : Nat) where
  readAddress : Net (addressType addressWidth)
  writeAddress : Net (addressType addressWidth)
  inputReady : Net .bit
  outputValid : Net .bit
  readAdvance : Net .bit
  writeAdvance : Net .bit

/-- Place a pointer controller under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (readPointer writePointer : Net (pointerType addressWidth))
    (inputValid outputReady : Net .bit) : Builder (PlacedOutputs addressWidth) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design addressWidth) fun
      | .readPointer => readPointer
      | .writePointer => writePointer
      | .inputValid => inputValid
      | .outputReady => outputReady
  pure {
    readAddress := child .readAddress
    writeAddress := child .writeAddress
    inputReady := child .inputReady
    outputValid := child .outputValid
    readAdvance := child .readAdvance
    writeAdvance := child .writeAdvance }

/-- Place a pointer controller using the next conventional indexed name. -/
noncomputable def place
    (readPointer writePointer : Net (pointerType addressWidth))
    (inputValid outputReady : Net .bit) : Builder (PlacedOutputs addressWidth) := do
  let child ← placeIndexed "fifo_pointer_control" (design addressWidth) fun
    | .readPointer => readPointer
    | .writePointer => writePointer
    | .inputValid => inputValid
    | .outputReady => outputReady
  pure {
    readAddress := child .readAddress
    writeAddress := child .writeAddress
    inputReady := child .inputReady
    outputValid := child .outputValid
    readAdvance := child .readAdvance
    writeAdvance := child .writeAdvance }

attribute [circuit_description] placeNamed place

end Silean.Modules.Fifo.PointerControl
