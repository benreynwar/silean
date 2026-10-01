import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.Increment.IncrementDerived
import Silean.Semantics.BoundaryTrace

/-! # Final-reorder frame control

This controller counts cycles within a marked frame and derives the two bank
write addresses, the common read address, the input/output half swaps, and the
single read-during-write bypass condition used by the final reorder.
-/

namespace HTFFT.Silean.FinalReorder.Control

open _root_.Silean

abbrev Address (addressWidth : Nat) := Fin addressWidth → Bool

def zeroAddress (addressWidth : Nat) : Address addressWidth :=
  BitVector.ofNat addressWidth 0

def oneAddress (addressWidth : Nat) : Address addressWidth :=
  BitVector.ofNat addressWidth 1

def lastAddress (addressWidth : Nat) : Address addressWidth :=
  fun _ => true

@[simp] theorem increment_zeroAddress (addressWidth : Nat) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (zeroAddress addressWidth) =
      oneAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  simp [zeroAddress, oneAddress]

theorem increment_ofNat (addressWidth value : Nat)
    (nextInRange : value + 1 < BitVector.cardinality addressWidth) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (BitVector.ofNat addressWidth value) =
      BitVector.ofNat addressWidth (value + 1) := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  simp only [BitVector.toNat_ofNat]
  have valueInRange : value < BitVector.cardinality addressWidth := by omega
  rw [Nat.mod_eq_of_lt valueInRange, Nat.mod_eq_of_lt nextInRange]

@[simp] theorem increment_lastAddress (addressWidth : Nat) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (lastAddress addressWidth) =
      zeroAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  have lastValue : BitVector.toNat addressWidth (lastAddress addressWidth) =
      BitVector.cardinality addressWidth - 1 := by
    induction addressWidth with
    | zero => rfl
    | succ width induction =>
      rw [BitVector.toNat]
      change BitVector.cardinality width +
          BitVector.toNat width (lastAddress width) = _
      rw [induction]
      have positive : 0 < BitVector.cardinality width := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos width
      simp only [BitVector.cardinality]
      omega
  rw [lastValue]
  have positive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  rw [Nat.sub_add_cancel positive]
  simp [zeroAddress]

@[simp] theorem increment_ofNat_cardinality_sub_one (addressWidth : Nat) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (BitVector.ofNat addressWidth
          (BitVector.cardinality addressWidth - 1)) =
      zeroAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  simp only [BitVector.toNat_ofNat]
  have positive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  have less : BitVector.cardinality addressWidth - 1 <
      BitVector.cardinality addressWidth := Nat.sub_lt positive (by omega)
  rw [Nat.mod_eq_of_lt less, Nat.sub_add_cancel positive]
  simp [zeroAddress]

@[ext] structure State (addressWidth : Nat) where
  storedWriteAddress : Address addressWidth
  storedReadAddress : Address addressWidth

module_ports ports (addressWidth : Nat) where
  input i_first : .bit,
  input i_readFirst : .bit,
  output o_writeAddress0 : .vector addressWidth .bit,
  output o_writeAddress1 : .vector addressWidth .bit,
  output o_readAddress : .vector addressWidth .bit,
  output o_writeSwap : .bit,
  output o_readSwap : .bit,
  output o_bypass : .bit

/-- The marker is synchronous with the first data word, so it selects zero
for the current cycle rather than resetting only the following cycle. -/
def effectiveAddress (addressWidth : Nat) (first : Bool)
    (storedAddress : Address addressWidth) : Address addressWidth :=
  bif first then zeroAddress addressWidth else storedAddress

/-- Rotate the frame counter right by one bit. This is the first bank's write
address: its high bit is the input-cycle parity. -/
def writeAddress0 (addressWidth : Nat) (address : Address addressWidth) :
    Address addressWidth :=
  fun index =>
    if nextInRange : index.val + 1 < addressWidth then
      address ⟨index.val + 1, nextInRange⟩
    else
      address ⟨0, Nat.zero_lt_of_lt index.isLt⟩

/-- The second bank uses the complementary address half. -/
def writeAddress1 (addressWidth : Nat) (address : Address addressWidth) :
    Address addressWidth :=
  fun index =>
    if nextInRange : index.val + 1 < addressWidth then
      address ⟨index.val + 1, nextInRange⟩
    else
      !address ⟨0, Nat.zero_lt_of_lt index.isLt⟩

/-- The independent read counter directly supplies the sequential bank read
address. It is reset by the half-frame-delayed marker. -/
def readAddress (addressWidth : Nat) (address : Address addressWidth) :
    Address addressWidth :=
  address

def lowBit (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  if positive : 0 < addressWidth then address ⟨0, positive⟩ else false

def highBit (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  if positive : 0 < addressWidth then
    address ⟨addressWidth - 1, Nat.sub_lt positive (by omega)⟩
  else
    false

def writeSwap (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  lowBit addressWidth address

def readSwap (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  highBit addressWidth address

def bypass (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  (SignalType.vector addressWidth .bit).equal address
    (lastAddress addressWidth)

def nextState (addressWidth : Nat) (first readFirst : Bool)
    (state : State addressWidth) : State addressWidth :=
  { storedWriteAddress :=
      _root_.Silean.Modules.Increment.incrementValue addressWidth
        (effectiveAddress addressWidth first state.storedWriteAddress)
    storedReadAddress :=
      _root_.Silean.Modules.Increment.incrementValue addressWidth
        (effectiveAddress addressWidth readFirst state.storedReadAddress) }

def outputMatches (addressWidth : Nat) (first readFirst : Bool)
    (state : State addressWidth)
    (output : (ports addressWidth).outputs.Values) : Prop :=
  let write := effectiveAddress addressWidth first state.storedWriteAddress
  let read := effectiveAddress addressWidth readFirst state.storedReadAddress
  output .o_writeAddress0 = writeAddress0 addressWidth write ∧
    output .o_writeAddress1 = writeAddress1 addressWidth write ∧
    output .o_readAddress = readAddress addressWidth read ∧
    output .o_writeSwap = writeSwap addressWidth write ∧
    output .o_readSwap = readSwap addressWidth read ∧
    output .o_bypass = bypass addressWidth write

def Transition (addressWidth : Nat)
    (input : (ports addressWidth).inputs.Values)
    (current : State addressWidth)
    (output : (ports addressWidth).outputs.Values)
    (next : State addressWidth) : Prop :=
  outputMatches addressWidth (input .i_first) (input .i_readFirst)
      current output ∧
    next = nextState addressWidth (input .i_first) (input .i_readFirst) current

/-- A finite boundary trace follows the controller from some deliberately
hidden initial counter value. -/
def contract (addressWidth : Nat)
    (trace : BoundaryTrace (ports addressWidth)) : Prop :=
  ∃ initial final,
    Trace (Transition addressWidth) initial trace.inputs trace.outputs final

end HTFFT.Silean.FinalReorder.Control
