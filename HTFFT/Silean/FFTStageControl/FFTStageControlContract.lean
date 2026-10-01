import HTFFT.Silean.FFTStage.Internal.FFTStageSchedule
import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlStructure
import Silean.Semantics.BoundaryTrace
import Silean.Semantics.FixedLatency

/-! # Natural trace contract for shared rolled-stage control -/

namespace HTFFT.Silean.FFTStageControl

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.Silean.FFTStage.Internal

def pairDelay (phaseExponent : Nat) := 2 ^ phaseExponent

@[simp] theorem pairDelay_pos (phaseExponent : Nat) :
    0 < pairDelay phaseExponent := by
  simp [pairDelay]

theorem phaseCardinality_eq_period (phaseExponent : Nat) :
    BitVector.cardinality (Internal.phaseWidth phaseExponent) =
      2 * pairDelay phaseExponent := by
  rw [BitVector.cardinality_eq_pow]
  simp [Internal.phaseWidth, pairDelay, Nat.pow_succ, Nat.mul_comm]

/-- The control block is exactly the control projection of the already
approved pure commutator.  Its irrelevant data paths carry `PUnit`. -/
abbrev State (phaseExponent : Nat) :=
  Commutator.State (pairDelay phaseExponent) PUnit

def inputValue (phaseExponent : Nat)
    (input : (ports (Internal.phaseWidth phaseExponent)).inputs.Values) :
    Commutator.Input PUnit :=
  { first := input .i_first, a := (), b := () }

def phaseBits (phaseExponent : Nat)
    (phase : Fin (2 * pairDelay phaseExponent)) :
    Fin (Internal.phaseWidth phaseExponent) → Bool :=
  BitVector.ofNat (Internal.phaseWidth phaseExponent) phase.val

/-- Interpret the hardware phase word as the pure commutator phase. -/
def phaseOfBits (phaseExponent : Nat)
    (bits : Fin (Internal.phaseWidth phaseExponent) → Bool) :
    Fin (2 * pairDelay phaseExponent) :=
  Fin.cast (phaseCardinality_eq_period phaseExponent)
    (BitVector.toIndex (Internal.phaseWidth phaseExponent) bits)

@[simp] theorem phaseOfBits_val (phaseExponent : Nat)
    (bits : Fin (Internal.phaseWidth phaseExponent) → Bool) :
    (phaseOfBits phaseExponent bits).val =
      BitVector.toNat (Internal.phaseWidth phaseExponent) bits := by
  simp [phaseOfBits]

@[simp] theorem phaseBits_phaseOfBits (phaseExponent : Nat)
    (bits : Fin (Internal.phaseWidth phaseExponent) → Bool) :
    phaseBits phaseExponent (phaseOfBits phaseExponent bits) = bits := by
  apply BitVector.toNat_injective
  unfold phaseBits
  rw [BitVector.toNat_ofNat, phaseOfBits_val]
  exact Nat.mod_eq_of_lt
    (BitVector.toNat_lt_cardinality _ bits)

@[simp] theorem phaseOfBits_phaseZero (phaseExponent : Nat) :
    phaseOfBits phaseExponent (Internal.phaseZero phaseExponent) =
      Commutator.phaseOfNat (pairDelay phaseExponent)
        (pairDelay_pos phaseExponent) 0 := by
  apply Fin.ext
  simp [Internal.phaseZero, Commutator.phaseOfNat]

@[simp] theorem phaseOfBits_phaseOne (phaseExponent : Nat) :
    phaseOfBits phaseExponent (Internal.phaseOne phaseExponent) =
      Commutator.phaseOfNat (pairDelay phaseExponent)
        (pairDelay_pos phaseExponent) 1 := by
  apply Fin.ext
  rw [phaseOfBits_val, show Internal.phaseOne phaseExponent =
    BitVector.ofNat (Internal.phaseWidth phaseExponent) 1 by rfl,
    BitVector.toNat_ofNat]
  simp only [Commutator.phaseOfNat, Fin.val_mk]
  rw [phaseCardinality_eq_period]

@[simp] theorem phaseOfBits_increment (phaseExponent : Nat)
    (bits : Fin (Internal.phaseWidth phaseExponent) → Bool) :
    phaseOfBits phaseExponent
        (Increment.incrementValue (Internal.phaseWidth phaseExponent) bits) =
      Commutator.phaseOfNat (pairDelay phaseExponent)
        (pairDelay_pos phaseExponent)
        (BitVector.toNat (Internal.phaseWidth phaseExponent) bits + 1) := by
  apply Fin.ext
  rw [phaseOfBits_val, Increment.incrementValue_toNat]
  simp only [Commutator.phaseOfNat, Fin.val_mk]
  rw [phaseCardinality_eq_period]

/-- The most-significant phase bit is exactly the commutator half selector. -/
theorem inFirstHalf_phaseOfBits (phaseExponent : Nat)
    (bits : Fin (Internal.phaseWidth phaseExponent) → Bool) :
    Commutator.inFirstHalf (pairDelay phaseExponent)
        (phaseOfBits phaseExponent bits) =
      !bits (Fin.last phaseExponent) := by
  unfold Commutator.inFirstHalf
  rw [phaseOfBits_val]
  change decide
      (BitVector.toNat (phaseExponent + 1) bits < 2 ^ phaseExponent) = _
  have lowerBound := BitVector.toNat_lt_cardinality phaseExponent
    (fun index => bits index.castSucc)
  rw [BitVector.cardinality_eq_pow] at lowerBound
  cases high : bits (Fin.last phaseExponent)
  · simpa [BitVector.toNat, high] using lowerBound
  · simp [BitVector.toNat, high, BitVector.cardinality_eq_pow]

/-- Selecting zero on a marked cycle is the bit-level form of the pure
commutator's effective phase. -/
theorem phaseBits_effectivePhase (phaseExponent : Nat)
    (stored : Fin (Internal.phaseWidth phaseExponent) → Bool) (first : Bool) :
    phaseBits phaseExponent
        (Commutator.effectivePhase (pairDelay phaseExponent)
          (pairDelay_pos phaseExponent) (phaseOfBits phaseExponent stored)
          first) =
      bif first then Internal.phaseZero phaseExponent else stored := by
  cases first with
  | false => simp [Commutator.effectivePhase]
  | true =>
      unfold Commutator.effectivePhase
      simp only [↓reduceIte]
      apply BitVector.toNat_injective
      simp [phaseBits, Commutator.phaseOfNat, Internal.phaseZero]

/-- The enabled-reset counter update is the bit-level form of the pure
commutator's phase update. -/
theorem phaseOfBits_nextValue (phaseExponent : Nat)
    (stored : Fin (Internal.phaseWidth phaseExponent) → Bool) (reset : Bool) :
    phaseOfBits phaseExponent
        (EnabledResetCounter.nextValue (Internal.phaseWidth phaseExponent)
          (Internal.phaseOne phaseExponent) true reset stored) =
      Commutator.nextPhase (pairDelay phaseExponent)
        (pairDelay_pos phaseExponent) (phaseOfBits phaseExponent stored)
        reset := by
  cases reset with
  | false =>
      change phaseOfBits phaseExponent
        (Increment.incrementValue (Internal.phaseWidth phaseExponent) stored) = _
      rw [phaseOfBits_increment]
      apply Fin.ext
      simp [Commutator.nextPhase, Commutator.effectivePhase,
        Commutator.phaseOfNat, phaseOfBits_val]
  | true =>
      simp [EnabledResetCounter.nextValue]

def outputMatches (phaseExponent : Nat) (state : State phaseExponent)
    (input : (ports (Internal.phaseWidth phaseExponent)).inputs.Values)
    (output : (ports (Internal.phaseWidth phaseExponent)).outputs.Values) : Prop :=
  let visible := Commutator.signals (pairDelay phaseExponent)
    (pairDelay_pos phaseExponent) state (inputValue phaseExponent input)
  output .o_delayedFirst = visible.delayedFirst ∧
    output .o_firstHalf = visible.firstHalf ∧
    output .o_outputPhase = phaseBits phaseExponent visible.outputPhase

def Transition (phaseExponent : Nat)
    (input : (ports (Internal.phaseWidth phaseExponent)).inputs.Values)
    (current : State phaseExponent)
    (output : (ports (Internal.phaseWidth phaseExponent)).outputs.Values)
    (next : State phaseExponent) : Prop :=
  outputMatches phaseExponent current input output ∧
    next = Commutator.nextState (pairDelay phaseExponent)
      (pairDelay_pos phaseExponent) current (inputValue phaseExponent input)

/-- A finite boundary trace follows the pure commutator control projection
from some hidden initial state. -/
def contract (phaseExponent : Nat)
    (trace : BoundaryTrace (ports (Internal.phaseWidth phaseExponent))) : Prop :=
  ∃ initial final,
    Trace (Transition phaseExponent) initial trace.inputs trace.outputs final

private theorem markerDelayTrace_of_controlTrace
    (phaseExponent : Nat)
    {initial final : State phaseExponent}
    {inputs : List
      (ports (Internal.phaseWidth phaseExponent)).inputs.Values}
    {outputs : List
      (ports (Internal.phaseWidth phaseExponent)).outputs.Values}
    (trace : Trace (Transition phaseExponent) initial inputs outputs final) :
    Trace (_root_.Silean.DelayLine.Step (pairDelay phaseExponent))
      initial.markerDelay (inputs.map fun input => (input .i_first : Bool))
      (outputs.map fun output => (output .o_delayedFirst : Bool))
      final.markerDelay := by
  induction trace with
  | nil => exact .nil _
  | cons inputValue outputValue transition rest ih =>
      rename_i current next final remainingInputs remainingOutputs
      have matched := transition.1
      have nextEqual := transition.2
      have outputEqual : (outputValue .o_delayedFirst : Bool) =
          FFTStage.Internal.DelayLine.output (pairDelay phaseExponent)
            (pairDelay_pos phaseExponent) current.markerDelay := by
        unfold outputMatches at matched
        simpa [Commutator.signals] using matched.1
      have stateEqual : next.markerDelay =
          FFTStage.Internal.DelayLine.next (pairDelay phaseExponent)
            (inputValue .i_first)
            current.markerDelay := by
        rw [nextEqual]
        rfl
      refine .cons (nextState := next.markerDelay)
        (inputValue .i_first) (outputValue .o_delayedFirst) ?_ ?_
      · constructor
        · simpa [ports, outputMap, SignalType.Denote,
            FFTStage.Internal.DelayLine.output] using outputEqual
        · intro index
          rw [stateEqual]
          rfl
      · exact ih

/-- The delayed marker exposed by the controller is exactly its input marker
after the commutator pair delay. -/
theorem delayedFirst_computes_of_contract
    (phaseExponent : Nat)
    {trace : BoundaryTrace (ports (Internal.phaseWidth phaseExponent))}
    (holds : contract phaseExponent trace) :
    FixedLatency.Computes (pairDelay phaseExponent) id
      (trace.inputs.map fun input => (input .i_first : Bool))
      (trace.outputs.map fun output => (output .o_delayedFirst : Bool)) := by
  obtain ⟨initial, final, controlTrace⟩ := holds
  have delayTrace := markerDelayTrace_of_controlTrace phaseExponent controlTrace
  unfold FixedLatency.Computes FixedLatency.Relates
  constructor
  · simpa using controlTrace.length_eq
  · intro t inputInTrace outputInTrace
    simpa only [id_eq] using
      (_root_.Silean.DelayLine.input_reaches_output delayTrace t
        inputInTrace outputInTrace)

end HTFFT.Silean.FFTStageControl
