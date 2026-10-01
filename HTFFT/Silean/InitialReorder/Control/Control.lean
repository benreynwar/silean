import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.Increment.IncrementDerived
import Silean.Semantics.BoundaryTrace

/-! # Initial-reorder frame control

This controller exposes the address within the current streamed frame and an
orientation bit selecting which of two physical register-bank layouts is in
use.  A marked cycle is always address zero.  The orientation is deliberately
not reset: it changes after every complete address traversal, so no reset or
distinguished initial orientation is required.
-/

namespace HTFFT.Silean.InitialReorder.Control

open _root_.Silean

abbrev Address (addressWidth : Nat) := Fin addressWidth → Bool

def zeroAddress (addressWidth : Nat) : Address addressWidth :=
  BitVector.ofNat addressWidth 0

def oneAddress (addressWidth : Nat) : Address addressWidth :=
  BitVector.ofNat addressWidth 1

def lastAddress (addressWidth : Nat) : Address addressWidth :=
  fun _ => true

@[simp] theorem toNat_lastAddress : ∀ addressWidth : Nat,
    BitVector.toNat addressWidth (lastAddress addressWidth) =
      BitVector.cardinality addressWidth - 1
  | 0 => rfl
  | addressWidth + 1 => by
      rw [BitVector.toNat]
      change BitVector.cardinality addressWidth +
          BitVector.toNat addressWidth (lastAddress addressWidth) = _
      rw [toNat_lastAddress addressWidth]
      have positive : 0 < BitVector.cardinality addressWidth := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth
      simp only [BitVector.cardinality]
      omega

@[simp] theorem ofNat_cardinality_sub_one (addressWidth : Nat) :
    BitVector.ofNat addressWidth
        (BitVector.cardinality addressWidth - 1) =
      lastAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [BitVector.toNat_ofNat, toNat_lastAddress]
  have positive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  exact Nat.mod_eq_of_lt (Nat.sub_lt positive (by omega))

@[ext] structure State (addressWidth : Nat) where
  storedAddress : Address addressWidth
  reversed : Bool

module_ports ports (addressWidth : Nat) where
  input i_first : .bit,
  output o_address : .vector addressWidth .bit,
  output o_reversed : .bit

/-- Address used on the current cycle.  `i_first` is synchronized with the
first data word, so it affects that same cycle rather than the next one. -/
def effectiveAddress (addressWidth : Nat) (first : Bool)
    (state : State addressWidth) : Address addressWidth :=
  bif first then zeroAddress addressWidth else state.storedAddress

def atLastAddress (addressWidth : Nat) (address : Address addressWidth) : Bool :=
  decide (BitVector.toNat addressWidth address =
    BitVector.cardinality addressWidth - 1)

@[simp] theorem atLastAddress_eq_true_iff (addressWidth : Nat)
    (address : Address addressWidth) :
    atLastAddress addressWidth address = true ↔
      address = lastAddress addressWidth := by
  simp only [atLastAddress, decide_eq_true_eq]
  constructor
  · intro equal
    apply BitVector.toNat_injective addressWidth
    simpa using equal
  · intro equal
    rw [equal, toNat_lastAddress]

@[simp] theorem increment_zeroAddress (addressWidth : Nat) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (zeroAddress addressWidth) =
      oneAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  simp [zeroAddress, oneAddress]

/-- Incrementing the encoding of an in-range address produces the encoding of
the following address.  The explicit bound rules out the wrapping case. -/
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

/-- The final address wraps to zero. -/
@[simp] theorem increment_lastAddress (addressWidth : Nat) :
    _root_.Silean.Modules.Increment.incrementValue addressWidth
        (lastAddress addressWidth) =
      zeroAddress addressWidth := by
  apply BitVector.toNat_injective addressWidth
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat,
    toNat_lastAddress]
  have positive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  rw [Nat.sub_add_cancel positive]
  simp [zeroAddress]

@[simp] theorem increment_orientation (value : Bool) :
    _root_.Silean.Modules.Increment.incrementValue 1 (fun _ => value) =
      (fun _ => !value) := by
  apply BitVector.toNat_injective 1
  rw [_root_.Silean.Modules.Increment.incrementValue_toNat]
  cases value <;> rfl

@[simp] theorem increment_orientation_at (value : Fin 1 → Bool) :
    _root_.Silean.Modules.Increment.incrementValue 1 value 0 = !value 0 := by
  have eta : value = fun _ => value 0 := by
    funext index
    exact congrArg value (Subsingleton.elim index 0)
  rw [eta, increment_orientation]

/-- State after one cycle.  Reaching the last address toggles the physical
orientation; a marker realigns only the within-frame address. -/
def nextState (addressWidth : Nat) (first : Bool)
    (state : State addressWidth) : State addressWidth :=
  let address := effectiveAddress addressWidth first state
  { storedAddress :=
      _root_.Silean.Modules.Increment.incrementValue addressWidth address
    reversed := bif atLastAddress addressWidth address then
      !state.reversed else state.reversed }

def outputMatches (addressWidth : Nat) (first : Bool)
    (state : State addressWidth)
    (output : (ports addressWidth).outputs.Values) : Prop :=
  output .o_address = effectiveAddress addressWidth first state ∧
    output .o_reversed = state.reversed

def Transition (addressWidth : Nat)
    (input : (ports addressWidth).inputs.Values)
    (current : State addressWidth)
    (output : (ports addressWidth).outputs.Values)
    (next : State addressWidth) : Prop :=
  outputMatches addressWidth (input .i_first) current output ∧
    next = nextState addressWidth (input .i_first) current

/-- A finite boundary trace follows the natural address/orientation machine
from some deliberately hidden initial state. -/
def contract (addressWidth : Nat)
    (trace : BoundaryTrace (ports addressWidth)) : Prop :=
  ∃ initial final,
    Trace (Transition addressWidth) initial trace.inputs trace.outputs final

end HTFFT.Silean.InitialReorder.Control
