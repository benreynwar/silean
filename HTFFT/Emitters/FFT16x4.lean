import HTFFT.Silean.FFT
import Silean.FIRRTL.Emit

/-! A concrete 16-point, four-samples-per-cycle FFT used by the generated-RTL
regression.  Its arithmetic and pipeline choices are deliberately explicit so
the cocotb model can check exact fixed-point results and exact latency. -/

namespace HTFFT.Emitters.FFT16x4

open Silean
open HTFFT.FixedPoint
open HTFFT.Silean

def butterflyPipeline : PipelinedFixedButterfly.Pipeline where
  registerInputs := true
  complexMultiply :=
    { multiplierLatency := 1
      registerBeforeRounding := true }
  registerProduct := true
  registerOutputs := true

/-- Register the middle boundary of each two-bit barrel shifter. -/
def barrelPipeline : Silean.Modules.BarrelShifter.Pipeline 2 where
  registerBoundary boundary := boundary.val == 1

def configuration : FFT.Configuration 4 where
  inputFormat := ⟨12, 8⟩
  twiddleFractionalBits := fun _ => 8
  twiddleFractionalBits_min := by decide
  laneDepth := 2
  laneDepth_pos := by decide
  laneDepth_le_depth := by decide
  initialReorderGeometry := by decide
  initialBarrelPipeline := barrelPipeline
  unrolledButterflyPipeline := fun _ => butterflyPipeline
  unrolledBoundaryLatency := fun boundary =>
    if boundary.val == 1 then 1 else 0
  rolledButterflyPipeline := fun _ => butterflyPipeline
  rolledTwiddleDefinitionName := fun stage =>
    s!"htfft_16x4_twiddle_stage_{stage.val + 2}"

#guard configuration.frameLength == 4
#guard configuration.laneCount == 4
#guard configuration.totalLatency == 33

/-- Numeric specialization of the generic generator and quantization bound,
kept beside the concrete RTL configuration for use by its cocotb test. -/
theorem twiddleError_le_coarse_bound (stage : Fin 4) :
    configuration.twiddleError stage ≤ Real.sqrt 2 / 128 := by
  rw [FFT.Configuration.twiddleError]
  have generated := configuration.twiddleGenerationError_le_quantum stage
  have sqrtNonnegative := Real.sqrt_nonneg 2
  calc
    _ ≤ Real.sqrt 2 *
        (HTFFT.Fixed.quantum (configuration.arithmetic.twiddleFormat stage) +
          HTFFT.Fixed.quantum (configuration.arithmetic.twiddleFormat stage)) :=
      mul_le_mul_of_nonneg_left (add_le_add generated le_rfl) sqrtNonnegative
    _ = Real.sqrt 2 / 128 := by
      simp [configuration, FFT.Configuration.arithmetic,
        HTFFT.Fixed.TwiddleGenerator.q2Format, HTFFT.Fixed.quantum]
      ring

def naming :=
  (FFT.naming 4 configuration).withKey ⟨"htfft_16x4", "", []⟩

def firrtl : Silean.FIRRTL.RenderResult String :=
  Silean.FIRRTL.renderCircuit naming

end HTFFT.Emitters.FFT16x4

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-htfft-16x4" args
    HTFFT.Emitters.FFT16x4.firrtl
