import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterflyDerived
import HTFFT.Silean.UnrolledFFTLayer.UnrolledFFTLayer
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Constant.Constant
import Silean.Naming.SignalAdapterNaming

/-! Structural implementation of one generic unrolled FFT layer. -/

namespace HTFFT.Silean.UnrolledFFTLayer.Internal

open _root_.Silean
open HTFFT.FixedPoint

/-- A butterfly is identified naturally by its group and twiddle offset. -/
abbrev ButterflyIndex (depth : Nat) (stage : Fin depth) :=
  Fin (2 ^ (depth - stage.val - 1)) × Fin (2 ^ stage.val)

/-- Lexicographic traversal of the layer's butterfly family. -/
@[reducible] def butterflyEnumeration (depth : Nat) (stage : Fin depth) :
    Enumeration (ButterflyIndex depth stage) :=
  Enumeration.product
    (Enumeration.fin (2 ^ (depth - stage.val - 1)))
    (Enumeration.fin (2 ^ stage.val))

/-- The full pure layer position selected by one butterfly and branch. -/
def position (index : ButterflyIndex depth stage) (branch : Fin 2) :
    HTFFT.Exact.LayerPosition depth stage where
  group := index.1
  branch := branch
  offset := index.2

/-- Input/output vector position belonging to one butterfly branch. -/
def sampleIndex (index : ButterflyIndex depth stage) (branch : Fin 2) :
    Fin (2 ^ depth) :=
  HTFFT.Exact.layerIndexEquiv depth stage (position index branch)

/-- Recover the butterfly owning an output sample. -/
def butterflyIndexOfSample (sample : Fin (2 ^ depth)) :
    ButterflyIndex depth stage :=
  let position := (HTFFT.Exact.layerIndexEquiv depth stage).symm sample
  (position.group, position.offset)

/-- Recover whether a sample is the upper or lower output of its butterfly. -/
def branchOfSample (stage : Fin depth) (sample : Fin (2 ^ depth)) : Fin 2 :=
  ((HTFFT.Exact.layerIndexEquiv depth stage).symm sample).branch

@[simp] theorem butterflyIndexOfSample_sampleIndex
    (index : ButterflyIndex depth stage) (branch : Fin 2) :
    butterflyIndexOfSample (sampleIndex index branch) = index := by
  simp [butterflyIndexOfSample, sampleIndex, position]

@[simp] theorem branchOfSample_sampleIndex
    (index : ButterflyIndex depth stage) (branch : Fin 2) :
    branchOfSample stage (sampleIndex index branch) = branch := by
  simp [branchOfSample, sampleIndex, position]

/-- Aggregate adapter for the layer's input samples. -/
@[reducible] def inputSplitter
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth) :
    Composition.SignalSplitter :=
  .vector (2 ^ depth)
    (complexSignalType (configuration.boundaryFormat stage.castSucc))

/-- Aggregate adapter for the layer's output samples. -/
@[reducible] def outputCombiner
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth) :
    Composition.SignalCombiner :=
  .vector (2 ^ depth)
    (complexSignalType (configuration.boundaryFormat stage.succ))

/-- Packed signal type of the twiddle table consumed by one layer. -/
def twiddleTableType (configuration : UnrolledFFT.Configuration depth)
    (stage : Fin depth) : SignalType :=
  .vector (2 ^ stage.val)
    (complexSignalType (configuration.twiddleFormat stage))

/-- Packed twiddle table consumed by all groups in a layer. -/
def twiddleValues (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    (twiddleTableType configuration stage).Denote :=
  fun offset =>
    PipelinedFixedButterfly.encodeComplex
      (configuration.twiddleFormat stage).width
      (table.value stage offset)

/-- Aggregate adapter exposing individual static twiddles. -/
@[reducible] def twiddleSplitter
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth) :
    Composition.SignalSplitter :=
  .vector (2 ^ stage.val)
    (complexSignalType (configuration.twiddleFormat stage))

/-- A butterfly's grown component width is the next pure layer boundary
width. -/
theorem butterflyOutputWidth_eq
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth) :
    PipelinedFixedButterfly.outputComponentWidth
        (configuration.boundaryFormat stage.castSucc) =
      (configuration.boundaryFormat stage.succ).width := by
  simp [
    PipelinedFixedButterfly.outputComponentWidth_eq,
    FFTConfiguration.boundaryFormat]
  omega

/-- The packed butterfly output type is exactly the next pure layer boundary
type.  The cast induced by this equality is structural typing only; it emits
no hardware and changes no bits. -/
theorem butterflyOutputType_eq
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth) :
    .vector
        (PipelinedFixedButterfly.outputComponentWidth
            (configuration.boundaryFormat stage.castSucc) +
          PipelinedFixedButterfly.outputComponentWidth
            (configuration.boundaryFormat stage.castSucc))
        .bit =
      complexSignalType (configuration.boundaryFormat stage.succ) :=
  congrArg (fun width => SignalType.vector (width + width) .bit)
    (butterflyOutputWidth_eq configuration stage)

/-- Value-level transport corresponding to `butterflyOutputType_eq`. -/
def castButterflyOutput
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth)
    (value : Fin
      (PipelinedFixedButterfly.outputComponentWidth
          (configuration.boundaryFormat stage.castSucc) +
        PipelinedFixedButterfly.outputComponentWidth
          (configuration.boundaryFormat stage.castSucc)) → Bool) :
    (complexSignalType (configuration.boundaryFormat stage.succ)).Denote :=
  Eq.mp
    (congrArg SignalType.Denote
      (butterflyOutputType_eq configuration stage)) value

private theorem castDenote_eq_mp {sourceType targetType : SignalType}
    (equal : sourceType = targetType) (value : sourceType.Denote) :
    equal ▸ value = Eq.mp (congrArg SignalType.Denote equal) value := by
  cases equal
  rfl

/-- The value transport performed by `SignalSource.castType` is the named
value-level transport used by the arithmetic proof. -/
theorem castTypeValue_eq_castButterflyOutput
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth)
    (value : Fin
      (PipelinedFixedButterfly.outputComponentWidth
          (configuration.boundaryFormat stage.castSucc) +
        PipelinedFixedButterfly.outputComponentWidth
          (configuration.boundaryFormat stage.castSucc)) → Bool) :
    butterflyOutputType_eq configuration stage ▸ value =
      castButterflyOutput configuration stage value :=
  castDenote_eq_mp (butterflyOutputType_eq configuration stage) value

private theorem cast_encodeComplex_of_width_eq
    {leftWidth rightWidth : Nat} (equal : leftWidth = rightWidth)
    (typeEqual :
      SignalType.vector (leftWidth + leftWidth) .bit =
        SignalType.vector (rightWidth + rightWidth) .bit)
    (value : HTFFT.Complex Int) :
    Eq.mp
      (congrArg SignalType.Denote typeEqual)
        (PipelinedFixedButterfly.encodeComplex leftWidth value) =
      PipelinedFixedButterfly.encodeComplex rightWidth value := by
  cases equal
  cases typeEqual
  rfl

/-- Transporting an encoded complex value to the propositionally equal next
boundary type preserves the encoded value. -/
theorem cast_encodeComplex
    (configuration : UnrolledFFT.Configuration depth) (stage : Fin depth)
    (value : HTFFT.Complex Int) :
    castButterflyOutput configuration stage
        (PipelinedFixedButterfly.encodeComplex
          (PipelinedFixedButterfly.outputComponentWidth
            (configuration.boundaryFormat stage.castSucc)) value) =
      PipelinedFixedButterfly.encodeComplex
        (configuration.boundaryFormat stage.succ).width value := by
  unfold castButterflyOutput complexSignalType
  exact cast_encodeComplex_of_width_eq
    (butterflyOutputWidth_eq configuration stage)
    (butterflyOutputType_eq configuration stage) value

/-- Stable emission identity for the complete static layer specialization. -/
def specialization (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    List _root_.Silean.Naming.ModuleParameter :=
  let dataFormat := configuration.boundaryFormat stage.castSucc
  let twiddleFormat := configuration.twiddleFormat stage
  let pipeline := configuration.butterflyPipeline stage
  [.natural depth, .natural stage.val,
    .natural dataFormat.width, .natural dataFormat.fractionalBits,
    .natural twiddleFormat.width, .natural twiddleFormat.fractionalBits,
    .boolean pipeline.registerInputs,
    .natural pipeline.complexMultiply.multiplierLatency,
    .boolean pipeline.complexMultiply.registerBeforeRounding,
    .boolean pipeline.registerProduct,
    .boolean pipeline.registerOutputs] ++
    _root_.Silean.Modules.Constant.Naming.parameters
      (twiddleTableType configuration stage)
      (twiddleValues configuration table stage)

end HTFFT.Silean.UnrolledFFTLayer.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design UnrolledFFTLayer
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (variant := s!"stage_{stage.val}")
    (specialization :=
      UnrolledFFTLayer.Internal.specialization configuration table stage) where
  boundary (UnrolledFFTLayer.ports configuration stage)
    (naming := UnrolledFFTLayer.Naming.ports configuration stage)
  instances {
    inputSplit := Naming.SignalAdapter.splitterDesign
      (UnrolledFFTLayer.Internal.inputSplitter configuration stage),
    twiddleTable := Constant.design
      (UnrolledFFTLayer.Internal.twiddleTableType configuration stage)
      (UnrolledFFTLayer.Internal.twiddleValues configuration table stage),
    twiddleSplit := Naming.SignalAdapter.splitterDesign
      (UnrolledFFTLayer.Internal.twiddleSplitter configuration stage),
    butterfly
        (index : UnrolledFFTLayer.Internal.ButterflyIndex depth stage in
          UnrolledFFTLayer.Internal.butterflyEnumeration depth stage)
        (name := .indexed "butterfly"
          (index.1.val * 2 ^ stage.val + index.2.val)) :=
      PipelinedFixedButterfly.design
        (configuration.boundaryFormat stage.castSucc).width
        (configuration.boundaryFormat stage.castSucc).fractionalBits
        (configuration.twiddleFormat stage).width
        (configuration.twiddleFormat stage).fractionalBits
        (configuration.butterflyPipeline stage).registerInputs
        (configuration.butterflyPipeline stage).complexMultiply.multiplierLatency
        (configuration.butterflyPipeline stage).complexMultiply.registerBeforeRounding
        (configuration.butterflyPipeline stage).registerProduct
        (configuration.butterflyPipeline stage).registerOutputs,
    outputCombine := Naming.SignalAdapter.combinerDesign
      (UnrolledFFTLayer.Internal.outputCombiner configuration stage) }
  wiring {
    outputs {
      .output := outputCombine.value }
    instance (.inputSplit) {
      .value := input.input }
    instance (.twiddleTable) {}
    instance (.twiddleSplit) {
      .value := twiddleTable.output }
    instance (.butterfly index) {
      .a := inputSplit[UnrolledFFTLayer.Internal.sampleIndex index 0],
      .b := inputSplit[UnrolledFFTLayer.Internal.sampleIndex index 1],
      .twiddle := twiddleSplit[index.2] }
    instance (.outputCombine) {
      sample := from (
        let index :=
          UnrolledFFTLayer.Internal.butterflyIndexOfSample
            (stage := stage) sample
        let branch :=
          UnrolledFFTLayer.Internal.branchOfSample
            stage sample
        let context := UnrolledFFTLayer.context depth configuration table stage
        if branch = 0 then
          SignalSource.castType
            (UnrolledFFTLayer.Internal.butterflyOutputType_eq
              configuration stage)
            (context.instanceOutput (.butterfly index) .upper)
        else
          SignalSource.castType
            (UnrolledFFTLayer.Internal.butterflyOutputType_eq
              configuration stage)
            (context.instanceOutput (.butterfly index) .lower)) }
  }

end HTFFT.Silean
