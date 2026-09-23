import Silean.FIRRTL
import HTFFT.Silean.PipelinedSignedComplexMultiply

namespace HTFFTTests.PipelinedSignedComplexMultiply

open Silean Silean.FIRRTL
open HTFFT.Silean.PipelinedSignedComplexMultiply

private def pipeline (multiplierLatency : Nat)
    (registerBeforeRounding : Bool := false) : Pipeline :=
  { multiplierLatency, registerBeforeRounding }

private abbrev structureFor
    (leftWidth rightWidth discardedWidth : Nat) (selected : Pipeline) :=
  moduleStructure leftWidth rightWidth discardedWidth
    selected.multiplierLatency selected.registerBeforeRounding

private def namingFor
    (leftWidth rightWidth discardedWidth : Nat) (selected : Pipeline) :=
  naming leftWidth rightWidth discardedWidth
    selected.multiplierLatency selected.registerBeforeRounding

private def fixedConfig : HTFFT.Butterfly.Fixed.Config :=
  { dataFormat := ⟨4, 2⟩
    twiddleFormat := ⟨3, 1⟩
    productFormat := ⟨7, 2⟩
    outputFormat := ⟨8, 2⟩
    rounding := .nearestTiesToEven }

def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputValues (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag rightReal rightImag : Int) :
    (ports leftWidth rightWidth discardedWidth).inputs.Values
  | .leftReal => signedBits leftWidth leftReal
  | .leftImag => signedBits leftWidth leftImag
  | .rightReal => signedBits rightWidth rightReal
  | .rightImag => signedBits rightWidth rightImag

def decodedReal (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Int) (rightReal rightImag : Int) : Int :=
  (BitVector.toBitVec (resultWidth leftWidth rightWidth discardedWidth)
    (realResultValue leftWidth rightWidth discardedWidth
      (signedBits leftWidth leftReal) (signedBits leftWidth leftImag)
      (signedBits rightWidth rightReal) (signedBits rightWidth rightImag))).toInt

def decodedImag (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Int) (rightReal rightImag : Int) : Int :=
  (BitVector.toBitVec (resultWidth leftWidth rightWidth discardedWidth)
    (imagResultValue leftWidth rightWidth discardedWidth
      (signedBits leftWidth leftReal) (signedBits leftWidth leftImag)
      (signedBits rightWidth rightReal) (signedBits rightWidth rightImag))).toInt

example (leftWidth rightWidth discardedWidth : Nat) (selected : Pipeline) :
    ModuleStructuralCertification
      (structureFor leftWidth rightWidth discardedWidth selected) :=
  structuralCertification leftWidth rightWidth discardedWidth selected

example (leftWidth rightWidth discardedWidth : Nat) (selected : Pipeline)
    {initialState finalState :
      (structureFor leftWidth rightWidth discardedWidth selected).State}
    {inputs : List (ports leftWidth rightWidth discardedWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth discardedWidth).outputs.Values}
    (execution :
      (structureFor leftWidth rightWidth discardedWidth selected).Executes
        initialState inputs outputs finalState) :
    contract leftWidth rightWidth discardedWidth selected
      execution.toBoundaryTrace :=
  contract_of_execution
    leftWidth rightWidth discardedWidth selected execution

#check place

#guard (pipeline 0).latency == 0
#guard (pipeline 3).latency == 3
#guard (pipeline 0 true).latency == 1
#guard (pipeline 3 true).latency == 4

-- Both components are exact when no low bits are discarded.
#guard decodedReal 4 3 0 3 1 2 (-1) == 7
#guard decodedImag 4 3 0 3 1 2 (-1) == -1

-- Positive and negative halfway cases choose the even quotient, after the
-- two scalar products have been combined.
#guard decodedReal 4 4 1 3 1 2 1 == 2
#guard decodedImag 4 4 1 3 1 2 1 == 2
#guard decodedReal 4 4 1 (-1) 0 3 0 == -2
#guard decodedReal 4 4 1 1 0 7 0 == 4

-- Unequal and zero operand widths use the same total public interface.
#guard decodedReal 3 5 2 (-3) 2 7 (-4) == -3
#guard decodedImag 3 5 2 (-3) 2 7 (-4) == 6
#guard decodedReal 0 4 3 0 0 (-7) 3 == 0
#guard decodedImag 0 4 3 0 0 (-7) 3 == 0

-- Nat subtraction makes an excessive discard request a zero-width result.
#guard resultWidth 4 3 8 == 0
#guard resultWidth 4 3 9 == 0
#guard resultWidth 0 0 2 == 0

-- The separate HTFFT bridge identifies the same contract values with the
-- pure fixed-point fused complex product when its unwrapped result fits.
example :
    HTFFT.FixedPoint.interpretSigned
        (BitVector.toBitVec (resultWidth 4 3 1)
          (realResultValue 4 3 1
            (signedBits 4 3) (signedBits 4 1)
            (signedBits 3 2) (signedBits 3 (-1)))) =
          (HTFFT.Butterfly.Fixed.multiplyRounded fixedConfig
            (complexValue 4 (signedBits 4 3) (signedBits 4 1))
            (complexValue 3 (signedBits 3 2) (signedBits 3 (-1)))).real ∧
      HTFFT.FixedPoint.interpretSigned
        (BitVector.toBitVec (resultWidth 4 3 1)
          (imagResultValue 4 3 1
            (signedBits 4 3) (signedBits 4 1)
            (signedBits 3 2) (signedBits 3 (-1)))) =
          (HTFFT.Butterfly.Fixed.multiplyRounded fixedConfig
            (complexValue 4 (signedBits 4 3) (signedBits 4 1))
            (complexValue 3 (signedBits 3 2) (signedBits 3 (-1)))).imag := by
  apply resultValues_eq_multiplyRounded
  · rfl
  · rfl
  · change HTFFT.FixedPoint.FitsWidth 7 4
    norm_num [HTFFT.FixedPoint.FitsWidth, HTFFT.FixedPoint.signedMin,
      HTFFT.FixedPoint.signedMax]
  · change HTFFT.FixedPoint.FitsWidth 7 0
    norm_num [HTFFT.FixedPoint.FitsWidth, HTFFT.FixedPoint.signedMin,
      HTFFT.FixedPoint.signedMax]

-- The structural trace theorem aligns all four products at the selected
-- latency, independently of the arbitrary initial register contents.
example (initialState : (structureFor 4 3 1 (pipeline 0)).State) :
    ∃ outputs finalState,
      (structureFor 4 3 1 (pipeline 0)).Executes initialState
        [inputValues 4 3 1 3 1 2 (-1)] outputs finalState ∧
      ∃ outputInTrace : 0 < outputs.length,
        outputs.get ⟨0, outputInTrace⟩ .resultReal =
            realResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) ∧
          outputs.get ⟨0, outputInTrace⟩ .resultImag =
            imagResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 4 3 1 (pipeline 0)).hasSolution.execution_exists
      initialState [inputValues 4 3 1 3 1 2 (-1)]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 0 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  have accepted := FixedLatency.relation_at_of_trace execution
    (contract_of_execution 4 3 1 (pipeline 0) execution)
    0 (by simp) outputInTrace
  simpa [inputValues, Pipeline.latency, pipeline] using
    accepted

example (initialState : (structureFor 4 3 1 (pipeline 2)).State) :
    ∃ outputs finalState,
      (structureFor 4 3 1 (pipeline 2)).Executes initialState
        [inputValues 4 3 1 3 1 2 (-1),
          inputValues 4 3 1 0 0 0 0,
          inputValues 4 3 1 1 (-2) 3 1]
        outputs finalState ∧
      ∃ outputInTrace : 2 < outputs.length,
        outputs.get ⟨2, outputInTrace⟩ .resultReal =
            realResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) ∧
          outputs.get ⟨2, outputInTrace⟩ .resultImag =
            imagResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 4 3 1 (pipeline 2)).hasSolution.execution_exists
      initialState
      [inputValues 4 3 1 3 1 2 (-1),
        inputValues 4 3 1 0 0 0 0,
        inputValues 4 3 1 1 (-2) 3 1]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 2 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  have accepted := FixedLatency.relation_at_of_trace execution
    (contract_of_execution 4 3 1 (pipeline 2) execution)
    0 (by simp) outputInTrace
  simpa [inputValues, Pipeline.latency, pipeline] using
    accepted

-- The optional synchronized numerator register adds exactly one cycle after
-- the Add/Sub and before both rounders.
example (initialState : (structureFor 4 3 1 (pipeline 0 true)).State) :
    ∃ outputs finalState,
      (structureFor 4 3 1 (pipeline 0 true)).Executes initialState
        [inputValues 4 3 1 3 1 2 (-1),
          inputValues 4 3 1 0 0 0 0] outputs finalState ∧
      ∃ outputInTrace : 1 < outputs.length,
        outputs.get ⟨1, outputInTrace⟩ .resultReal =
            realResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) ∧
          outputs.get ⟨1, outputInTrace⟩ .resultImag =
            imagResultValue 4 3 1
              (signedBits 4 3) (signedBits 4 1)
              (signedBits 3 2) (signedBits 3 (-1)) := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 4 3 1
      (pipeline 0 true)).hasSolution.execution_exists initialState
      [inputValues 4 3 1 3 1 2 (-1),
        inputValues 4 3 1 0 0 0 0]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 1 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  have accepted := FixedLatency.relation_at_of_trace execution
    (contract_of_execution 4 3 1 (pipeline 0 true) execution)
    0 (by simp) outputInTrace
  simpa [inputValues, Pipeline.latency, pipeline] using accepted

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape
    (leftWidth rightWidth discardedWidth : Nat)
    (selected : Pipeline) : Bool :=
  match renderRootModule
      (namingFor leftWidth rightWidth discardedWidth selected) with
  | .error _ => false
  | .ok text =>
      occurrences text "inst pipelined_signed_multiply_" == 4 &&
      occurrences text "inst sub_" == 1 &&
      occurrences text "inst add_" == 1 &&
      occurrences text "inst combine_numerators" == 1 &&
      occurrences text "inst register_before_rounding" == 1 &&
      occurrences text "inst split_numerators" == 1 &&
      occurrences text "inst vector_layout_" == 2 &&
      occurrences text "inst signed_round_shift_" == 2

#guard rootHasShape 4 3 2 (pipeline 0)
#guard rootHasShape 4 3 2 (pipeline 3)
#guard rootHasShape 4 3 9 (pipeline 1 true)
#guard rootHasShape 0 4 5 (pipeline 2 true)

#guard match renderRootModule (namingFor 4 3 2 (pipeline 1)) with
  | .error _ => false
  | .ok text =>
      contains text "public module PipelinedSignedComplexMultiply_4_3_2_1" &&
      contains text "output resultReal : UInt<1>[6]" &&
      contains text "connect sub_0.left, pipelined_signed_multiply_0.result" &&
      contains text "connect sub_0.right, pipelined_signed_multiply_1.result" &&
      contains text "connect add_0.left, pipelined_signed_multiply_2.result" &&
      contains text "connect add_0.right, pipelined_signed_multiply_3.result" &&
      contains text "connect signed_round_shift_0.value, vector_layout_0.output" &&
      contains text "connect signed_round_shift_1.value, vector_layout_1.output"

#guard match renderCircuit (namingFor 4 3 2 (pipeline 1)) with
  | .error _ => false
  | .ok text =>
      contains text "public module PipelinedSignedComplexMultiply_4_3_2_1" &&
      contains text "module PipelinedSignedMultiply_4_3_1" &&
      contains text "module SignedRoundShift_6_2" &&
      contains text "module FullAdder"

end HTFFTTests.PipelinedSignedComplexMultiply
