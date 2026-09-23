import Silean.FIRRTL
import HTFFT.Fixed.Twiddle8Accuracy
import HTFFT.Silean.UnrolledFFT

namespace HTFFTTests.UnrolledFFT

open Silean Silean.FIRRTL
open HTFFT
open HTFFT.Fixed
open HTFFT.FixedPoint
open HTFFT.Silean

private def pipeline : PipelinedFixedButterfly.Pipeline where
  registerInputs := false
  complexMultiply :=
    { multiplierLatency := 0
      registerBeforeRounding := false }
  registerProduct := false
  registerOutputs := false

/-- Lightweight eight-point hardware instance using the certified Q2.8
twiddle table and the existing Q4.8 input policy. -/
def configuration : UnrolledFFT.Configuration 3 where
  inputFormat := ⟨12, 8⟩
  twiddleFormat _ := Fixed.Twiddle8.twiddleFormat
  butterflyPipeline _ := pipeline
  boundaryLatency _ := 0

theorem fixedConfig_eq :
    configuration.fixedConfig = Fixed.Twiddle8.config := by
  rfl

theorem twiddlesFit :
    configuration.TwiddlesFit Fixed.Twiddle8.table := by
  apply FFTConfiguration.TwiddlesFit.ofAccuracy
    configuration.toFFTConfiguration Fixed.Twiddle8.table
      Fixed.Twiddle8.twiddleError
  simpa only [fixedConfig_eq] using Fixed.Twiddle8.accuracy

theorem carriersCover : configuration.ProductCarriersCover := by
  intro stage
  apply PipelinedFixedButterfly.productCarrierCoversData_of_fractionalBits_le_width
  norm_num [configuration, Fixed.Twiddle8.twiddleFormat]

#guard configuration.networkLatency == 0

example : ModuleStructuralCertification
    (UnrolledFFT.moduleStructure 3 configuration Fixed.Twiddle8.table) :=
  UnrolledFFT.structuralCertification configuration Fixed.Twiddle8.table

example
    {initialState finalState :
      (UnrolledFFT.moduleStructure 3 configuration
        Fixed.Twiddle8.table).State}
    {inputs : List (UnrolledFFT.ports configuration).inputs.Values}
    {outputs : List (UnrolledFFT.ports configuration).outputs.Values}
    (execution :
      (UnrolledFFT.moduleStructure 3 configuration Fixed.Twiddle8.table).Executes
        initialState inputs outputs finalState) :
    UnrolledFFT.contract configuration Fixed.Twiddle8.table
      execution.toBoundaryTrace :=
  UnrolledFFT.contract_of_execution configuration Fixed.Twiddle8.table
    twiddlesFit carriersCover execution

-- The public hardware-result bridge specializes to the already certified
-- concrete eight-point DFT error bound.
example
    (input : Fin 8 →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote)
    (output : Fin 8 →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last 3))).Denote)
    (outputCorrect : output =
      UnrolledFFTLayer.encodeVector
        (configuration.boundaryFormat (Fin.last 3))
        (UnrolledFFT.resultValue configuration Fixed.Twiddle8.table input))
    (inputMagnitude : MagnitudeBound 1
      (decodeVector configuration.fixedConfig 0
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input)))
    (index : Fin 8) :
    ‖UnrolledFFT.decodeOutput configuration output index -
        ZMod.dft
          (Exact.toZModVector
            (decodeVector configuration.fixedConfig 0
              (UnrolledFFTLayer.decodeVector
                (configuration.boundaryFormat 0) input)))
          (Exact.zmodIndexEquiv 3 index)‖ ≤
      25 * Real.sqrt 2 / 256 + 9 / 32768 := by
  have noOverflow : NoOverflow configuration.fixedConfig Fixed.Twiddle8.table
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input) := by
    rw [fixedConfig_eq]
    apply Fixed.Twiddle8.noOverflow_of_input_magnitude
    simpa only [← fixedConfig_eq] using inputMagnitude
  have bounded := UnrolledFFT.output_pointwise_dft configuration
    Fixed.Twiddle8.table Fixed.Twiddle8.twiddleError input output
    (decodeVector configuration.fixedConfig 0
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input))
    { magnitude := 1, error := 0 } outputCorrect
    (by constructor <;> norm_num)
    (by simpa only [fixedConfig_eq] using Fixed.Twiddle8.accuracy)
    inputMagnitude (by intro inputIndex; simp) noOverflow index
  rw [fixedConfig_eq, Fixed.Twiddle8.decoded_bounds] at bounded
  exact bounded

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

-- Concrete Q2.8 eight-point elaboration and FIRRTL smoke test.
#guard match renderCircuit
    (UnrolledFFT.naming 3 configuration Fixed.Twiddle8.table) with
  | .error _ => false
  | .ok text =>
      contains text "public module UnrolledFFT" &&
      contains text "inst reorder" &&
      contains text "inst network" &&
      contains text "module UnrolledFFTNetwork" &&
      contains text "module UnrolledFFTLayer" &&
      contains text "module PipelinedFixedButterfly"

end HTFFTTests.UnrolledFFT
