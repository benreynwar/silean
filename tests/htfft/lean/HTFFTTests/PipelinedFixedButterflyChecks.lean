import Silean.FIRRTL
import HTFFT.Silean.PipelinedFixedButterfly

namespace HTFFTTests.PipelinedFixedButterfly

open Silean Silean.FIRRTL
open HTFFT
open HTFFT.FixedPoint
open HTFFT.Silean.PipelinedFixedButterfly

private def pipeline (input : Bool) (multiplierLatency : Nat)
    (beforeRounding product output : Bool) : Pipeline :=
  { registerInputs := input
    complexMultiply := { multiplierLatency, registerBeforeRounding := beforeRounding }
    registerProduct := product
    registerOutputs := output }

private abbrev structureFor (dataFormat twiddleFormat : Format)
    (selected : Pipeline) :=
  moduleStructure dataFormat.width dataFormat.fractionalBits
    twiddleFormat.width twiddleFormat.fractionalBits
    selected.registerInputs selected.complexMultiply.multiplierLatency
    selected.complexMultiply.registerBeforeRounding
    selected.registerProduct selected.registerOutputs

private def namingFor (dataFormat twiddleFormat : Format)
    (selected : Pipeline) :=
  naming dataFormat.width dataFormat.fractionalBits
    twiddleFormat.width twiddleFormat.fractionalBits
    selected.registerInputs selected.complexMultiply.multiplierLatency
    selected.complexMultiply.registerBeforeRounding
    selected.registerProduct selected.registerOutputs

private def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

private def packed (width : Nat) (real imag : Int) :
    Fin (width + width) → Bool :=
  encodeComplex width ⟨real, imag⟩

private def inputValues (dataFormat twiddleFormat : Format)
    (aReal aImag bReal bImag twiddleReal twiddleImag : Int) :
    (ports dataFormat twiddleFormat).inputs.Values
  | .a => packed dataFormat.width aReal aImag
  | .b => packed dataFormat.width bReal bImag
  | .twiddle => packed twiddleFormat.width twiddleReal twiddleImag

private def dataFormat : Format := ⟨4, 2⟩
private def twiddleFormat : Format := ⟨4, 2⟩

private theorem carrier :
    ProductCarrierCoversData dataFormat twiddleFormat := by
  norm_num [ProductCarrierCoversData, dataFormat, twiddleFormat,
    HTFFT.Silean.PipelinedSignedComplexMultiply.resultWidth,
    HTFFT.Silean.PipelinedSignedComplexMultiply.numeratorWidth,
    HTFFT.Silean.PipelinedSignedComplexMultiply.productWidth,
    Silean.Modules.Arithmetic.resultWidth]

example (selected : Pipeline) :
    ModuleStructuralCertification
      (structureFor dataFormat twiddleFormat selected) :=
  structuralCertification dataFormat twiddleFormat selected

example (selected : Pipeline)
    {initialState finalState :
      (structureFor dataFormat twiddleFormat selected).State}
    {inputs : List (ports dataFormat twiddleFormat).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat).outputs.Values}
    (execution :
      (structureFor dataFormat twiddleFormat selected).Executes
        initialState inputs outputs finalState) :
    contract dataFormat twiddleFormat selected execution.toBoundaryTrace :=
  contract_of_execution dataFormat twiddleFormat selected carrier execution

#check place
#check output_eq_butterfly_of_execution
#check output_eq_outputRounded_of_execution

-- Every choice of the four optional boundaries contributes exactly one
-- cycle, independently of the two-cycle multiplier chain used here.
#guard (pipeline false 2 false false false).latency == 2
#guard (pipeline false 2 false false true).latency == 3
#guard (pipeline false 2 false true false).latency == 3
#guard (pipeline false 2 false true true).latency == 4
#guard (pipeline false 2 true false false).latency == 3
#guard (pipeline false 2 true false true).latency == 4
#guard (pipeline false 2 true true false).latency == 4
#guard (pipeline false 2 true true true).latency == 5
#guard (pipeline true 2 false false false).latency == 3
#guard (pipeline true 2 false false true).latency == 4
#guard (pipeline true 2 false true false).latency == 4
#guard (pipeline true 2 false true true).latency == 5
#guard (pipeline true 2 true false false).latency == 4
#guard (pipeline true 2 true false true).latency == 5
#guard (pipeline true 2 true true false).latency == 5
#guard (pipeline true 2 true true true).latency == 6

-- The fused product rounds once, is narrowed to four bits, and the final
-- Add/Sub grows only the high side to five bits.
#guard resultValue dataFormat twiddleFormat
    (packed 4 3 (-2)) (packed 4 2 1) (packed 4 2 (-1)) ==
  { upper := ⟨4, -2⟩, lower := ⟨2, -2⟩ }

-- Positive and negative halfway products use ties-to-even before the final
-- butterfly addition and subtraction.
#guard resultValue dataFormat twiddleFormat
    (packed 4 0 0) (packed 4 5 0) (packed 4 2 0) ==
  { upper := ⟨2, 0⟩, lower := ⟨-2, 0⟩ }
#guard resultValue dataFormat twiddleFormat
    (packed 4 0 0) (packed 4 (-5) 0) (packed 4 2 0) ==
  { upper := ⟨-2, 0⟩, lower := ⟨2, 0⟩ }

-- An actual fully-pipelined execution returns the first source input at the
-- total six-cycle displacement, regardless of arbitrary initial registers.
example (initialState :
    (structureFor dataFormat twiddleFormat
      (pipeline true 2 true true true)).State) :
    ∃ outputs finalState,
      (structureFor dataFormat twiddleFormat
        (pipeline true 2 true true true)).Executes initialState
        (List.replicate 7
          (inputValues dataFormat twiddleFormat 3 (-2) 2 1 2 (-1)))
        outputs finalState ∧
      ∃ outputInTrace :
          (pipeline true 2 true true true).latency < outputs.length,
        decodeComplex 5
            (outputs.get
              ⟨(pipeline true 2 true true true).latency, outputInTrace⟩
              .upper) = ⟨4, -2⟩ ∧
        decodeComplex 5
            (outputs.get
              ⟨(pipeline true 2 true true true).latency, outputInTrace⟩
              .lower) = ⟨2, -2⟩ := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification dataFormat twiddleFormat
      (pipeline true 2 true true true)).hasSolution.execution_exists
        initialState
        (List.replicate 7
          (inputValues dataFormat twiddleFormat 3 (-2) 2 1 2 (-1)))
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace :
      (pipeline true 2 true true true).latency < outputs.length := by
    simp at outputLength
    simp [pipeline, Pipeline.latency,
      HTFFT.Silean.PipelinedSignedComplexMultiply.Pipeline.latency]
    rw [outputLength]
    simp
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  have exactFixed := output_eq_butterfly_of_execution
    dataFormat twiddleFormat (pipeline true 2 true true true)
    carrier execution 0 (by simp) outputInTrace
  have arithmetic :
      resultValue dataFormat twiddleFormat
          (packed dataFormat.width 3 (-2))
          (packed dataFormat.width 2 1)
          (packed twiddleFormat.width 2 (-1)) =
        { upper := ⟨4, -2⟩, lower := ⟨2, -2⟩ } := by
    native_decide
  simp [inputValues] at exactFixed
  rw [arithmetic] at exactFixed
  convert exactFixed using 1 <;>
    simp [pipeline, Pipeline.latency,
      HTFFT.Silean.PipelinedSignedComplexMultiply.Pipeline.latency,
      dataFormat, twiddleFormat, outputComponentWidth,
      Silean.Modules.Arithmetic.resultWidth, Nat.max_def] <;>
    constructor <;> intro assumption <;> exact assumption

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (selected : Pipeline) : Bool :=
  match renderRootModule (namingFor dataFormat twiddleFormat selected) with
  | .error _ => false
  | .ok text =>
      occurrences text "inst input_register_" == 3 &&
      occurrences text "inst split_complex_" == 4 &&
      occurrences text "inst complex_multiply" == 1 &&
      occurrences text "inst product_boundary_" == 2 &&
      occurrences text "inst combine_product" == 1 &&
      occurrences text "inst register_product" == 1 &&
      occurrences text "inst align_a" == 1 &&
      occurrences text "inst add_" == 2 &&
      occurrences text "inst sub_" == 2 &&
      occurrences text "inst combine_output_" == 2 &&
      occurrences text "inst output_register_" == 2

#guard rootHasShape (pipeline false 0 false false false)
#guard rootHasShape (pipeline true 2 true true true)

#guard match renderRootModule
    (namingFor dataFormat twiddleFormat (pipeline true 2 true true true)) with
  | .error _ => false
  | .ok text =>
      contains text "output upper : UInt<1>[10]" &&
      contains text "connect complex_multiply.leftReal, split_complex_0.right" &&
      contains text "connect register_product.input, combine_product.result" &&
      contains text "connect add_0.right, split_complex_2.right" &&
      contains text "connect sub_1.right, split_complex_2.left"

#guard match renderCircuit
    (namingFor dataFormat twiddleFormat (pipeline true 2 true true true)) with
  | .error _ => false
  | .ok text =>
      contains text "public module PipelinedFixedButterfly" &&
      contains text "module PipelinedSignedComplexMultiply" &&
      contains text "module OptionalShiftRegister" &&
      contains text "module FullAdder"

end HTFFTTests.PipelinedFixedButterfly
