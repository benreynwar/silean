import HTFFT.Silean.FFTStage.Internal.FFTStageSchedule
import HTFFT.Silean.FFTStageLane.FFTStageLane
import Silean.Modules.ROM.ROM
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Semantics.BoundaryTrace
import Silean.Semantics.FixedLatency

/-! # Natural trace contract for one rolled-stage lane -/

namespace HTFFT.Silean.FFTStageLane

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint
open HTFFT.Silean.FFTStage.Internal

abbrev Value (dataFormat : Format) := (dataSignalType dataFormat).Denote

structure Invocation (phaseWidth : Nat) (dataFormat : Format) where
  outputPhase : Fin (BitVector.cardinality phaseWidth)
  operands : Commutator.Operands (Value dataFormat)

def inputPhase (phaseWidth : Nat)
    (bits : Fin phaseWidth → Bool) : Fin (BitVector.cardinality phaseWidth) :=
  BitVector.toIndex phaseWidth bits

@[simp] theorem phaseBits_inputPhase (phaseWidth : Nat)
    (bits : Fin phaseWidth → Bool) :
    BitVector.ofNat phaseWidth (inputPhase phaseWidth bits).val = bits := by
  apply BitVector.toNat_injective phaseWidth
  rw [BitVector.toNat_ofNat]
  rw [show (inputPhase phaseWidth bits).val =
    BitVector.toNat phaseWidth bits by simp [inputPhase]]
  exact Nat.mod_eq_of_lt
    (BitVector.toNat_lt_cardinality phaseWidth bits)

def firstDelayInput (dataFormat twiddleFormat : Format) (phaseWidth : Nat)
    (input : (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    : Value dataFormat :=
  bif input .i_firstHalf then input .i_branchA else input .i_branchB

def secondDelayInput (dataFormat twiddleFormat : Format) (phaseWidth : Nat)
    (input : (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    (secondOutput : Value dataFormat) : Value dataFormat :=
  bif input .i_firstHalf then input .i_branchB else secondOutput

def invocationValue (dataFormat twiddleFormat : Format) (phaseWidth : Nat)
    (input : (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    (firstOutput secondOutput : Value dataFormat) :
    Invocation phaseWidth dataFormat :=
  { outputPhase := inputPhase phaseWidth (input .i_outputPhase)
    operands := bif input .i_firstHalf then
      { a := secondOutput, b := firstOutput }
    else
      { a := firstOutput, b := input .i_branchA } }

def secondDelayInputs (dataFormat twiddleFormat : Format) (phaseWidth : Nat) :
    List (ports dataFormat twiddleFormat phaseWidth).inputs.Values →
      List (Value dataFormat) → List (Value dataFormat)
  | input :: inputs, output :: outputs =>
      secondDelayInput dataFormat twiddleFormat phaseWidth input output ::
        secondDelayInputs dataFormat twiddleFormat phaseWidth inputs outputs
  | _, _ => []

def invocationsOf (dataFormat twiddleFormat : Format) (phaseWidth : Nat) :
    List (ports dataFormat twiddleFormat phaseWidth).inputs.Values →
      List (Value dataFormat) → List (Value dataFormat) →
        List (Invocation phaseWidth dataFormat)
  | input :: inputs, firstOutput :: firstOutputs,
      secondOutput :: secondOutputs =>
      invocationValue dataFormat twiddleFormat phaseWidth input
          firstOutput secondOutput ::
        invocationsOf dataFormat twiddleFormat phaseWidth inputs
          firstOutputs secondOutputs
  | _, _, _ => []

@[simp] theorem secondDelayInputs_map (dataFormat twiddleFormat : Format)
    (phaseWidth : Nat) (values : List α)
    (input : α → (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    (secondOutput : α → Value dataFormat) :
    secondDelayInputs dataFormat twiddleFormat phaseWidth
        (values.map input) (values.map secondOutput) =
      values.map (fun value => secondDelayInput dataFormat twiddleFormat
        phaseWidth (input value) (secondOutput value)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [secondDelayInputs, induction]

@[simp] theorem invocationsOf_map (dataFormat twiddleFormat : Format)
    (phaseWidth : Nat) (values : List α)
    (input : α → (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    (firstOutput secondOutput : α → Value dataFormat) :
    invocationsOf dataFormat twiddleFormat phaseWidth
        (values.map input) (values.map firstOutput)
        (values.map secondOutput) =
      values.map (fun value => invocationValue dataFormat twiddleFormat
        phaseWidth (input value) (firstOutput value) (secondOutput value)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [invocationsOf, induction]

theorem length_invocationsOf (dataFormat twiddleFormat : Format)
    (phaseWidth : Nat)
    (inputs : List (ports dataFormat twiddleFormat phaseWidth).inputs.Values)
    (firstOutputs secondOutputs : List (Value dataFormat))
    (firstLength : firstOutputs.length = inputs.length)
    (secondLength : secondOutputs.length = inputs.length) :
    (invocationsOf dataFormat twiddleFormat phaseWidth inputs firstOutputs
      secondOutputs).length = inputs.length := by
  induction inputs generalizing firstOutputs secondOutputs with
  | nil =>
      simp only [List.length_nil] at firstLength secondLength
      cases firstOutputs <;> cases secondOutputs <;> simp_all [invocationsOf]
  | cons input inputs induction =>
      cases firstOutputs with
      | nil => simp at firstLength
      | cons firstOutput firstOutputs =>
          cases secondOutputs with
          | nil => simp at secondLength
          | cons secondOutput secondOutputs =>
              simp only [List.length_cons, Nat.succ.injEq] at firstLength secondLength
              simp [invocationsOf,
                induction firstOutputs secondOutputs firstLength secondLength]

def twiddleAddress (phaseWidth laneAddressWidth lane : Nat)
    (phase : Fin (BitVector.cardinality phaseWidth)) :
    Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) :=
  BitVector.toIndex (laneAddressWidth + phaseWidth)
    (VectorConcat.concat
      (BitVector.ofNat laneAddressWidth lane)
      (BitVector.ofNat phaseWidth phase.val))

def resultValue (dataFormat twiddleFormat : Format)
    (phaseWidth laneAddressWidth lane : Nat)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (invocation : Invocation phaseWidth dataFormat) :
    HTFFT.Butterfly.Result Int :=
  PipelinedFixedButterfly.resultValue dataFormat twiddleFormat
    invocation.operands.a invocation.operands.b
    (twiddleValues (twiddleAddress phaseWidth laneAddressWidth lane
      invocation.outputPhase))

def outputRelation (dataFormat twiddleFormat : Format)
    (phaseWidth laneAddressWidth lane : Nat)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (invocation : Invocation phaseWidth dataFormat)
    (output : (ports dataFormat twiddleFormat phaseWidth).outputs.Values) : Prop :=
  let result := resultValue dataFormat twiddleFormat phaseWidth
    laneAddressWidth lane twiddleValues invocation
  output .o_upper = PipelinedFixedButterfly.encodeComplex
      (PipelinedFixedButterfly.outputComponentWidth dataFormat) result.upper ∧
    output .o_lower = PipelinedFixedButterfly.encodeComplex
      (PipelinedFixedButterfly.outputComponentWidth dataFormat) result.lower

/-- The commutator delays produce one invocation per cycle; the butterfly
bank returns that invocation's fixed-point result after its selected latency.
Both internal delay states are existentially hidden. -/
def contract (dataFormat twiddleFormat : Format) (pairDelay : Nat)
    (_positive : 0 < pairDelay) (phaseWidth laneAddressWidth lane : Nat)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (trace : BoundaryTrace (ports dataFormat twiddleFormat phaseWidth)) : Prop :=
  ∃ firstOutputs secondOutputs invocations,
    FixedLatency.Computes pairDelay
        (firstDelayInput dataFormat twiddleFormat phaseWidth)
        trace.inputs firstOutputs ∧
      FixedLatency.Computes pairDelay id
        (secondDelayInputs dataFormat twiddleFormat phaseWidth
          trace.inputs secondOutputs) secondOutputs ∧
      invocations = invocationsOf dataFormat twiddleFormat phaseWidth
        trace.inputs firstOutputs secondOutputs ∧
      FixedLatency.Relates pipeline.latency
        (outputRelation dataFormat twiddleFormat phaseWidth laneAddressWidth lane
          twiddleValues)
        invocations trace.outputs

end HTFFT.Silean.FFTStageLane
