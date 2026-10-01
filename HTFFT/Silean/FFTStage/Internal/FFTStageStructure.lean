import HTFFT.Silean.FFTStage.Internal.FFTStageSchedule
import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlStructural
import HTFFT.Silean.FFTStageLane.Internal.FFTStageLaneStructural
import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterflyDerived
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived
import Silean.Modules.ROM.ROMDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived
import Silean.Modules.VectorConcat.VectorConcatDerived
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.NotPrimitive

/-! # Concrete shift-register FFT stage

This is the permanent structural realization of the pure commutator schedule.
Every parallel lane owns two positive `pairDelay` shift registers and one
butterfly.  Input phase controls the commutator muxes; the independently
rephased delayed-output phase controls the lane's twiddle ROM address.
-/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean
open HTFFT.FixedPoint

/-- Fixed-point data format entering the selected rolled stage. -/
abbrev dataFormat (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : Format :=
  configuration.boundaryFormat geometry.stage.castSucc

/-- Fixed-point data format leaving the selected rolled stage. -/
abbrev outputFormat (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : Format :=
  configuration.boundaryFormat geometry.stage.succ

/-- Packed signal carried by each commutator path. -/
abbrev dataSignalType (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : SignalType :=
  complexSignalType (dataFormat configuration geometry)

/-- Packed signal returned by each butterfly branch. -/
abbrev outputSignalType (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : SignalType :=
  complexSignalType (outputFormat configuration geometry)

/-- Packed static twiddle value read by each butterfly lane. -/
abbrev twiddleSignalType (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : SignalType :=
  complexSignalType (configuration.twiddleFormat geometry.stage)

/-- Number of low phase bits in the half-period `pairDelay`. -/
def phaseExponent (geometry : Geometry depth) : Nat :=
  geometry.stage.val - geometry.laneDepth

/-- Counter width for the complete `2 * pairDelay` commutator period. -/
def phaseWidth (geometry : Geometry depth) : Nat :=
  phaseExponent geometry + 1

/-- Number of low twiddle-address bits supplied by the parallel lane. -/
def laneAddressWidth (geometry : Geometry depth) : Nat :=
  geometry.laneDepth - 1

@[simp] theorem pairDelay_eq_two_pow_phaseExponent
    (geometry : Geometry depth) :
    geometry.pairDelay = 2 ^ phaseExponent geometry := by
  rfl

@[simp] theorem localPeriod_eq_phaseCardinality
    (geometry : Geometry depth) :
    geometry.localPeriod = BitVector.cardinality (phaseWidth geometry) := by
  rw [Geometry.localPeriod_eq_two_mul_pairDelay]
  rw [BitVector.cardinality_eq_pow]
  simp [phaseWidth, Nat.pow_succ, Nat.mul_comm,
    pairDelay_eq_two_pow_phaseExponent]

@[simp] theorem butterflyCount_eq_laneCardinality
    (geometry : Geometry depth) :
    butterflyCount geometry = BitVector.cardinality (laneAddressWidth geometry) := by
  simp [butterflyCount, BoundaryGeometry.lanesPerBranch,
    Geometry.inputBoundary, laneAddressWidth,
    BitVector.cardinality_eq_pow]

theorem addressWidth_eq (geometry : Geometry depth) :
    laneAddressWidth geometry + phaseWidth geometry = geometry.stage.val := by
  unfold laneAddressWidth phaseWidth phaseExponent
  have positive := geometry.laneDepth_pos
  have bounded := geometry.laneDepth_le_stage
  omega

/-- Structural type equality used after concatenating the static lane and
dynamic phase portions of a twiddle address. -/
theorem addressType_eq (geometry : Geometry depth) :
    SignalType.vector
        (laneAddressWidth geometry + phaseWidth geometry) .bit =
      SignalType.vector geometry.stage.val .bit :=
  congrArg (fun width => SignalType.vector width .bit)
    (addressWidth_eq geometry)

/-- A butterfly output component grows to exactly the next FFT boundary
width. -/
theorem butterflyOutputWidth_eq
    (configuration : FFTConfiguration depth) (geometry : Geometry depth) :
    PipelinedFixedButterfly.outputComponentWidth
        (dataFormat configuration geometry) =
      (outputFormat configuration geometry).width := by
  simp [PipelinedFixedButterfly.outputComponentWidth_eq,
    dataFormat, outputFormat, FFTConfiguration.boundaryFormat]
  omega

/-- Structural type equality between a butterfly branch and one packed stage
output lane. -/
theorem butterflyOutputType_eq
    (configuration : FFTConfiguration depth) (geometry : Geometry depth) :
    SignalType.vector
        (PipelinedFixedButterfly.outputComponentWidth
            (dataFormat configuration geometry) +
          PipelinedFixedButterfly.outputComponentWidth
            (dataFormat configuration geometry)) .bit =
      outputSignalType configuration geometry :=
  congrArg (fun width => SignalType.vector (width + width) .bit)
    (butterflyOutputWidth_eq configuration geometry)

/-- Value-level transport from a butterfly branch to the stage output lane. -/
def castButterflyOutput
    (configuration : FFTConfiguration depth) (geometry : Geometry depth)
    (value : (FFTStageLane.outputSignalType
      (dataFormat configuration geometry)).Denote) :
    (outputSignalType configuration geometry).Denote :=
  Eq.mp (congrArg SignalType.Denote
    (butterflyOutputType_eq configuration geometry)) value

private theorem castDenote_eq_mp {sourceType targetType : SignalType}
    (equal : sourceType = targetType) (value : sourceType.Denote) :
    equal ▸ value = Eq.mp (congrArg SignalType.Denote equal) value := by
  cases equal
  rfl

/-- The value transport inserted by structural wiring is the named transport
used by the stage proof. -/
theorem castTypeValue_eq_castButterflyOutput
    (configuration : FFTConfiguration depth) (geometry : Geometry depth)
    (value : (FFTStageLane.outputSignalType
      (dataFormat configuration geometry)).Denote) :
    butterflyOutputType_eq configuration geometry ▸ value =
      castButterflyOutput configuration geometry value :=
  castDenote_eq_mp (butterflyOutputType_eq configuration geometry) value

private theorem cast_encodeComplex_of_width_eq
    {leftWidth rightWidth : Nat} (equal : leftWidth = rightWidth)
    (typeEqual : SignalType.vector (leftWidth + leftWidth) .bit =
      SignalType.vector (rightWidth + rightWidth) .bit)
    (value : HTFFT.Complex Int) :
    Eq.mp (congrArg SignalType.Denote typeEqual)
        (PipelinedFixedButterfly.encodeComplex leftWidth value) =
      PipelinedFixedButterfly.encodeComplex rightWidth value := by
  cases equal
  cases typeEqual
  rfl

/-- Transport preserves an encoded complex value while changing only the
propositionally equal component width. -/
theorem cast_encodeComplex
    (configuration : FFTConfiguration depth) (geometry : Geometry depth)
    (value : HTFFT.Complex Int) :
    castButterflyOutput configuration geometry
        (PipelinedFixedButterfly.encodeComplex
          (PipelinedFixedButterfly.outputComponentWidth
            (dataFormat configuration geometry)) value) =
      PipelinedFixedButterfly.encodeComplex
        (outputFormat configuration geometry).width value := by
  unfold castButterflyOutput outputSignalType complexSignalType
  exact cast_encodeComplex_of_width_eq
    (butterflyOutputWidth_eq configuration geometry)
    (butterflyOutputType_eq configuration geometry) value

/-- Static encoded twiddle table read by every parallel ROM port. -/
def twiddleValues (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth) :
    Fin (_root_.Silean.Modules.ROM.entryCount
      (laneAddressWidth geometry + phaseWidth geometry)) →
      (twiddleSignalType configuration geometry).Denote :=
  fun address =>
    PipelinedFixedButterfly.encodeComplex
      (configuration.twiddleFormat geometry.stage).width
      (table.value geometry.stage
        (Fin.cast (by
          rw [show laneAddressWidth geometry + phaseWidth geometry =
            geometry.stage.val from addressWidth_eq geometry]
          exact BitVector.cardinality_eq_pow geometry.stage.val) address))

/-- The positive stage-pair delay packaged as a reusable child design.  Keeping
the proof inside this constructor prevents proof arguments from leaking into
the generated instance family. -/
def pairDelayDesign (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) : Naming.NamedModule :=
  _root_.Silean.Modules.ShiftRegister.design
    (dataSignalType configuration geometry)
    geometry.pairDelay (Geometry.pairDelay_pos geometry)

/-- The corresponding one-bit delay used to align the frame marker. -/
def markerDelayDesign (geometry : Geometry depth) : Naming.NamedModule :=
  _root_.Silean.Modules.ShiftRegister.design .bit geometry.pairDelay
    (Geometry.pairDelay_pos geometry)

/-- Reset value used by each phase counter.  The marked cycle is muxed to
phase zero; storing one makes the following cycle phase one. -/
def phaseOne (geometry : Geometry depth) :
    Fin (phaseWidth geometry) → Bool :=
  BitVector.ofNat (phaseWidth geometry) 1

/-- Combinational phase value selected on a marked cycle. -/
def phaseZero (geometry : Geometry depth) :
    Fin (phaseWidth geometry) → Bool :=
  BitVector.ofNat (phaseWidth geometry) 0

/-- Static low address bits assigned to one parallel butterfly lane. -/
def laneAddress (geometry : Geometry depth)
    (lane : Fin (butterflyCount geometry)) :
    Fin (laneAddressWidth geometry) → Bool :=
  BitVector.ofNat (laneAddressWidth geometry) lane.val

@[reducible] def inputSplitter
    (configuration : FFTConfiguration depth) (geometry : Geometry depth) :
    Composition.SignalSplitter :=
  .vector geometry.laneCount (dataSignalType configuration geometry)

@[reducible] def outputCombiner
    (configuration : FFTConfiguration depth) (geometry : Geometry depth) :
    Composition.SignalCombiner :=
  .vector geometry.laneCount (outputSignalType configuration geometry)

@[reducible] def phaseSplitter (geometry : Geometry depth) :
    Composition.SignalSplitter :=
  .vector (phaseWidth geometry) .bit

/-- Emission identity for the stage topology.  The ROM definition name owns
the table-content identity; this list records every remaining structural
choice made by the parent stage. -/
def specialization (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline) :
    List _root_.Silean.Naming.ModuleParameter :=
  let data := dataFormat configuration geometry
  let twiddle := configuration.twiddleFormat geometry.stage
  [.natural depth,
    .natural geometry.laneDepth,
    .natural geometry.stage.val,
    .natural data.width,
    .natural data.fractionalBits,
    .natural twiddle.width,
    .natural twiddle.fractionalBits,
    .boolean pipeline.registerInputs,
    .natural pipeline.complexMultiply.multiplierLatency,
    .boolean pipeline.complexMultiply.registerBeforeRounding,
    .boolean pipeline.registerProduct,
    .boolean pipeline.registerOutputs]

end HTFFT.Silean.FFTStage.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FFTStage
    (depth : Nat)
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : FFTStage.Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (variant := s!"stage_{geometry.stage.val}_{twiddleDefinitionName}")
    (specialization :=
      FFTStage.Internal.specialization configuration geometry pipeline) where
  boundary (FFTStage.ports configuration geometry)
    (naming := FFTStage.Naming.ports configuration geometry)
  instances {
    inputSplit := Naming.SignalAdapter.splitterDesign
      (FFTStage.Internal.inputSplitter configuration geometry),
    control := FFTStageControl.design
      (FFTStage.Internal.phaseExponent geometry),
    lane
        (lane : Fin (FFTStage.Internal.butterflyCount geometry) in
          Enumeration.fin (FFTStage.Internal.butterflyCount geometry))
        (name := .indexed "lane" lane.val) :=
      FFTStageLane.design
        (FFTStage.Internal.dataFormat configuration geometry)
        (configuration.twiddleFormat geometry.stage)
        (FFTStage.Internal.phaseExponent geometry)
        (FFTStage.Internal.phaseWidth geometry)
        (FFTStage.Internal.laneAddressWidth geometry) lane.val
        twiddleDefinitionName
        (FFTStage.Internal.twiddleValues configuration table geometry)
        pipeline,
    outputCombine := Naming.SignalAdapter.combinerDesign
      (FFTStage.Internal.outputCombiner configuration geometry),
    markerAlign := OptionalShiftRegister.design .bit pipeline.latency }
  wiring {
    outputs {
      .o_first := markerAlign.output,
      .o_data := outputCombine.value }
    instance (.inputSplit) {
      .value := input.i_data }
    instance (.control) {
      .i_first := input.i_first }
    instance (.lane lane) {
      .i_firstHalf := control.o_firstHalf,
      .i_outputPhase := control.o_outputPhase,
      .i_branchA := inputSplit[
        geometry.inputBoundary.laneEquiv.symm (0, lane)],
      .i_branchB := inputSplit[
        geometry.inputBoundary.laneEquiv.symm (1, lane)] }
    instance (.outputCombine) {
      sample := from (
        let branchLane := geometry.outputBoundary.laneEquiv sample
        let context := FFTStage.context depth configuration table geometry
          pipeline twiddleDefinitionName
        if branchLane.1 = 0 then
          SignalSource.castType
            (FFTStage.Internal.butterflyOutputType_eq configuration geometry)
            (context.instanceOutput (.lane branchLane.2) .o_upper)
        else
          SignalSource.castType
            (FFTStage.Internal.butterflyOutputType_eq configuration geometry)
            (context.instanceOutput (.lane branchLane.2) .o_lower)) }
    instance (.markerAlign) {
      .input := control.o_delayedFirst }
  }

end HTFFT.Silean
