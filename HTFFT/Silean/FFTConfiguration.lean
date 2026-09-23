import HTFFT.Fixed.Layered
import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterfly

/-! # Shared FFT hardware arithmetic configuration

This file contains the numeric policy shared by the different FFT hardware
organizations.  It deliberately does not contain choices about unrolling,
streaming delay structure, or pipeline placement.

The initial policy preserves the binary point and grows each signed component
by one high bit after every butterfly layer.
-/

namespace HTFFT.Silean

open HTFFT.FixedPoint

/-- Numeric choices shared by all power-of-two FFT hardware organizations. -/
structure FFTConfiguration (depth : Nat) where
  inputFormat : Format
  twiddleFormat : Fin depth → Format

/-- The fixed-point format at a selected layer boundary. -/
def FFTConfiguration.boundaryFormat
    (configuration : FFTConfiguration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) : Format :=
  { width := configuration.inputFormat.width + boundary.val
    fractionalBits := configuration.inputFormat.fractionalBits }

/-- The pure fixed-point configuration induced by the shared hardware
arithmetic policy. -/
def FFTConfiguration.fixedConfig
    (configuration : FFTConfiguration depth) : HTFFT.Fixed.Config depth where
  boundaryFormat := configuration.boundaryFormat
  twiddleFormat := configuration.twiddleFormat
  productFormat stage := configuration.boundaryFormat stage.castSucc
  rounding _ := .nearestTiesToEven

/-- Every stored twiddle is representable by the hardware format selected for
its layer.  Numerical twiddle certificates imply this condition directly. -/
def FFTConfiguration.TwiddlesFit (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) : Prop :=
  ∀ stage offset,
    ComplexFits (configuration.twiddleFormat stage)
      (table.value stage offset)

/-- Every layer's generic complex-multiplier result carrier is wide enough
for the explicit product boundary selected by the butterfly. -/
def FFTConfiguration.ProductCarriersCover
    (configuration : FFTConfiguration depth) : Prop :=
  ∀ stage,
    PipelinedFixedButterfly.ProductCarrierCoversData
      (configuration.boundaryFormat stage.castSucc)
      (configuration.twiddleFormat stage)

/-- A numerical twiddle-accuracy certificate supplies the hardware
representability condition without adding numerical error assumptions to the
structural contract. -/
theorem FFTConfiguration.TwiddlesFit.ofAccuracy
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (error : Fin depth → ℝ)
    (accuracy : HTFFT.Fixed.TwiddleAccuracy configuration.fixedConfig table error) :
    configuration.TwiddlesFit table :=
  accuracy.fits

@[simp] theorem FFTConfiguration.boundaryFormat_zero
    (configuration : FFTConfiguration depth) :
    configuration.boundaryFormat 0 = configuration.inputFormat := by
  cases configuration with
  | mk inputFormat twiddleFormat =>
      cases inputFormat
      rfl

@[simp] theorem FFTConfiguration.boundaryFormat_width
    (configuration : FFTConfiguration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) :
    (configuration.boundaryFormat boundary).width =
      configuration.inputFormat.width + boundary.val :=
  rfl

@[simp] theorem FFTConfiguration.boundaryFormat_fractionalBits
    (configuration : FFTConfiguration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) :
    (configuration.boundaryFormat boundary).fractionalBits =
      configuration.inputFormat.fractionalBits :=
  rfl

@[simp] theorem FFTConfiguration.fixedConfig_boundaryFormat
    (configuration : FFTConfiguration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) :
    configuration.fixedConfig.boundaryFormat boundary =
      configuration.boundaryFormat boundary :=
  rfl

@[simp] theorem FFTConfiguration.fixedConfig_twiddleFormat
    (configuration : FFTConfiguration depth) (stage : Fin depth) :
    configuration.fixedConfig.twiddleFormat stage =
      configuration.twiddleFormat stage :=
  rfl

@[simp] theorem FFTConfiguration.fixedConfig_productFormat
    (configuration : FFTConfiguration depth) (stage : Fin depth) :
    configuration.fixedConfig.productFormat stage =
      configuration.boundaryFormat stage.castSucc :=
  rfl

@[simp] theorem FFTConfiguration.fixedConfig_rounding
    (configuration : FFTConfiguration depth) (stage : Fin depth) :
    configuration.fixedConfig.rounding stage = .nearestTiesToEven :=
  rfl

/-- Each FFT layer uses exactly the butterfly arithmetic implemented by
`PipelinedFixedButterfly`. -/
theorem FFTConfiguration.butterfly_eq_fixedConfig
    (configuration : FFTConfiguration depth) (stage : Fin depth) :
    configuration.fixedConfig.butterfly stage =
      PipelinedFixedButterfly.fixedConfig
        (configuration.boundaryFormat stage.castSucc)
        (configuration.twiddleFormat stage) := by
  congr 1

end HTFFT.Silean
