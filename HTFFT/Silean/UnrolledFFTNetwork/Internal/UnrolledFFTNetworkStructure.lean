import HTFFT.Silean.UnrolledFFTLayer.UnrolledFFTLayerDerived
import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetwork
import Silean.Authoring.ModuleDesign
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived

/-! Flat alternating boundary-delay/layer structure of the unrolled network. -/

namespace HTFFT.Silean.UnrolledFFTNetwork.Internal

open _root_.Silean

/-- Complete packed sample-vector type at one layer boundary. -/
def samplesType (configuration : UnrolledFFT.Configuration depth)
    (boundary : HTFFT.Exact.LayerBoundary depth) : SignalType :=
  .vector (2 ^ depth)
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat boundary))

/-- The immediately preceding stage of a nonzero layer boundary. -/
def previousStage (boundary : HTFFT.Exact.LayerBoundary depth)
    (nonzero : boundary.val ≠ 0) : Fin depth :=
  ⟨boundary.val - 1, by omega⟩

@[simp] theorem previousStage_succ
    (boundary : HTFFT.Exact.LayerBoundary depth)
    (nonzero : boundary.val ≠ 0) :
    (previousStage boundary nonzero).succ = boundary := by
  apply Fin.ext
  simp [previousStage]
  omega

@[simp] theorem previousStage_of_succ (stage : Fin depth)
    (nonzero : (stage.succ : HTFFT.Exact.LayerBoundary depth).val ≠ 0) :
    previousStage stage.succ nonzero = stage := by
  apply Fin.succ_inj.mp
  exact previousStage_succ stage.succ nonzero

/-- Transport sample-vector types across equal layer boundaries. -/
theorem samplesType_eq
    (configuration : UnrolledFFT.Configuration depth)
    {left right : HTFFT.Exact.LayerBoundary depth}
    (equal : left = right) :
    samplesType configuration left = samplesType configuration right :=
  congrArg (samplesType configuration) equal

/-- Stable emission identity for the complete network specialization. -/
def specialization (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    List _root_.Silean.Naming.ModuleParameter :=
  [.natural depth,
   .natural configuration.inputFormat.width,
   .natural configuration.inputFormat.fractionalBits] ++
  ((List.finRange (depth + 1)).map fun boundary =>
    .natural (configuration.boundaryLatency boundary)) ++
  ((List.finRange depth).flatMap fun stage =>
    UnrolledFFTLayer.Internal.specialization configuration table stage)

end HTFFT.Silean.UnrolledFFTNetwork.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design UnrolledFFTNetwork
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (specialization :=
      UnrolledFFTNetwork.Internal.specialization configuration table) where
  boundary (UnrolledFFTNetwork.ports configuration)
    (naming := UnrolledFFTNetwork.Naming.ports configuration)
  instances {
    boundaryDelay
        (boundary : HTFFT.Exact.LayerBoundary depth in
          Enumeration.fin (depth + 1))
        (name := .indexed "boundary_delay" boundary.val) :=
      OptionalShiftRegister.design
        (UnrolledFFTNetwork.Internal.samplesType configuration boundary)
        (configuration.boundaryLatency boundary),
    layer (stage : Fin depth in Enumeration.fin depth)
        (name := .indexed "layer" stage.val) :=
      UnrolledFFTLayer.design depth configuration table stage }
  wiring {
    outputs {
      .output := boundaryDelay(Fin.last depth)[.output] }
    instance (.boundaryDelay boundary) {
      .input := from (
        let context := UnrolledFFTNetwork.context depth configuration table
        if zero : boundary.val = 0 then
          SignalSource.castType
            (UnrolledFFTNetwork.Internal.samplesType_eq configuration
              (Fin.ext zero.symm))
            (context.moduleInput .input)
        else
          let previous :=
            UnrolledFFTNetwork.Internal.previousStage boundary zero
          SignalSource.castType
            (UnrolledFFTNetwork.Internal.samplesType_eq configuration
              (UnrolledFFTNetwork.Internal.previousStage_succ
                boundary zero))
            (context.instanceOutput (.layer previous) .output)) }
    instance (.layer stage) {
      .input := boundaryDelay(stage.castSucc)[.output] }
  }

end HTFFT.Silean
