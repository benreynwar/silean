import HTFFT.Silean.FFT.Configuration
import HTFFT.Silean.FFTStage.FFTStage
import HTFFT.Silean.UnrolledFFTLayer.UnrolledFFTLayer

/-! # Complete FFT frame representations

Frames are ordinary finite functions of cycle and lane.  The helpers in this
file state how those physical coordinates denote one logical FFT vector at the
natural external boundary and at the two streamed internal boundaries.
-/

namespace HTFFT.Silean.FFT

/-- Packed complex data carried in one cycle at a selected fixed-point
format. -/
abbrev CycleData (configuration : Configuration depth)
    (format : HTFFT.FixedPoint.Format) :=
  Fin configuration.laneCount →
    (UnrolledFFTLayer.complexSignalType format).Denote

/-- One complete physical frame at a selected fixed-point format. -/
abbrev FrameData (configuration : Configuration depth)
    (format : HTFFT.FixedPoint.Format) :=
  _root_.Silean.FramedLatency.Frame configuration.frameLength
    (CycleData configuration format)

abbrev InputData (configuration : Configuration depth) :=
  CycleData configuration (configuration.arithmetic.boundaryFormat 0)

abbrev InputFrame (configuration : Configuration depth) :=
  FrameData configuration (configuration.arithmetic.boundaryFormat 0)

abbrev PrefixData (configuration : Configuration depth) :=
  FFTStage.BoundaryData configuration.arithmetic
    configuration.prefixGeometry

abbrev PrefixFrame (configuration : Configuration depth) :=
  FFTStage.BoundaryFrame configuration.arithmetic
    configuration.prefixGeometry

abbrev OutputData (configuration : Configuration depth) :=
  FFTStage.BoundaryData configuration.arithmetic
    configuration.finalGeometry

abbrev OutputFrame (configuration : Configuration depth) :=
  FFTStage.BoundaryFrame configuration.arithmetic
    configuration.finalGeometry

/-- Ordinary cycle-major interpretation of an external `(cycle, lane)`
coordinate. -/
def naturalLayout (configuration : Configuration depth) :
    (Fin configuration.frameLength × Fin configuration.laneCount) ≃
      Fin (2 ^ depth) :=
  finProdFinEquiv.trans (finCongr configuration.frame_cardinality)

@[simp] theorem naturalLayout_val (configuration : Configuration depth)
    (coordinate : Fin configuration.frameLength ×
      Fin configuration.laneCount) :
    (naturalLayout configuration coordinate).val =
      coordinate.2.val + configuration.laneCount * coordinate.1.val :=
  rfl

/-- At the boundary immediately following the lane-local prefix, the generic
streaming geometry is exactly ordinary cycle-major order. -/
theorem prefixGeometry_layout
    (configuration : Configuration depth) :
    configuration.prefixGeometry.layout =
      naturalLayout configuration := by
  unfold Configuration.prefixGeometry
  apply Equiv.ext
  intro coordinate
  apply Fin.ext
  simp only [FFTStage.BoundaryGeometry.layout_val]
  rw [FFTStage.BoundaryGeometry.laneEquiv_snd_val,
    FFTStage.BoundaryGeometry.cycleEquiv_snd_val,
    FFTStage.BoundaryGeometry.laneEquiv_fst_val,
    FFTStage.BoundaryGeometry.cycleEquiv_fst_val]
  unfold FFTStage.BoundaryGeometry.lanesPerBranch
    FFTStage.BoundaryGeometry.offsetsPerBranch
    FFTStage.BoundaryGeometry.batchCount
  change
    coordinate.2.val % 2 ^ (configuration.laneDepth - 1) +
        2 ^ (configuration.laneDepth - 1) *
          (coordinate.1.val % 2 ^
            (configuration.laneDepth - configuration.laneDepth)) +
        2 ^ (configuration.laneDepth - 1) *
          (coordinate.2.val / 2 ^ (configuration.laneDepth - 1)) +
        (2 * 2 ^ (configuration.laneDepth - 1)) *
          (coordinate.1.val / 2 ^
            (configuration.laneDepth - configuration.laneDepth)) =
      coordinate.2.val + 2 ^ configuration.laneDepth * coordinate.1.val
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.div_one,
    Nat.mul_zero, Nat.add_zero]
  have lanePower : 2 * 2 ^ (configuration.laneDepth - 1) =
      2 ^ configuration.laneDepth := by
    have exponent : configuration.laneDepth - 1 + 1 =
        configuration.laneDepth := by
      have lanePositive := configuration.laneDepth_pos
      omega
    calc
      2 * 2 ^ (configuration.laneDepth - 1) =
          2 ^ (configuration.laneDepth - 1) * 2 := by omega
      _ = 2 ^ (configuration.laneDepth - 1 + 1) := by
        rw [Nat.pow_succ]
      _ = 2 ^ configuration.laneDepth := by rw [exponent]
  rw [lanePower]
  rw [Nat.mod_add_div]

/-- Interpret any naturally ordered physical frame as one packed logical
vector. -/
def unpackNatural (configuration : Configuration depth)
    {format : HTFFT.FixedPoint.Format}
    (frame : FrameData configuration format) :
    Fin (2 ^ depth) → (UnrolledFFTLayer.complexSignalType format).Denote :=
  fun index =>
    let coordinate := (naturalLayout configuration).symm index
    frame coordinate.1 coordinate.2

/-- Unpacking through the prefix geometry is the same operation as ordinary
cycle-major unpacking. -/
@[simp] theorem prefixGeometry_unpack
    (configuration : Configuration depth)
    {format : HTFFT.FixedPoint.Format}
    (frame : FrameData configuration format) :
    configuration.prefixGeometry.unpack frame =
      unpackNatural configuration frame := by
  funext index
  simp [FFTStage.BoundaryGeometry.unpack, unpackNatural,
    prefixGeometry_layout]
  rfl

/-- Interpret an externally ordered input frame as one packed logical vector.
The prefix-boundary geometry is cycle-major before any rolled layer has
permuted the streamed layout. -/
def unpackInput (configuration : Configuration depth)
    (frame : InputFrame configuration) :
    Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat 0)).Denote :=
  unpackNatural configuration frame

/-- Arrange a packed logical result in natural external cycle-major order. -/
def packOutput (configuration : Configuration depth)
    (values : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat (Fin.last depth))).Denote) :
    OutputFrame configuration :=
  fun cycle lane => values (naturalLayout configuration (cycle, lane))

@[simp] theorem unpackInput_pack
    (configuration : Configuration depth)
    (values : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat 0)).Denote) :
    unpackInput configuration
        (fun cycle lane => values (naturalLayout configuration (cycle, lane))) =
      values := by
  funext index
  simp [unpackInput, unpackNatural]

@[simp] theorem packOutput_unpack
    (configuration : Configuration depth)
    (frame : OutputFrame configuration) :
    packOutput configuration
        (fun index =>
          let coordinate := (naturalLayout configuration).symm index
          frame coordinate.1 coordinate.2) = frame := by
  funext cycle lane
  simp [packOutput, naturalLayout]

/-- Decode the natural external input frame into the pure fixed-point model. -/
def decodeInput (configuration : Configuration depth)
    (frame : InputFrame configuration) : HTFFT.Fixed.Vector depth :=
  UnrolledFFTLayer.decodeVector
    (configuration.arithmetic.boundaryFormat 0)
    (unpackInput configuration frame)

/-- Decode the physical frame after the unrolled prefix. -/
def decodePrefix (configuration : Configuration depth)
    (frame : PrefixFrame configuration) : HTFFT.Fixed.Vector depth :=
  FFTStage.decodeBoundaryFrame configuration.arithmetic
    configuration.prefixGeometry frame

/-- The boundary-indexed prefix decoder agrees with the ordinary
cycle-major presentation used by the fixed-point prefix model. -/
theorem decodePrefix_eq_decodeVector_unpackNatural
    (configuration : Configuration depth)
    (frame : PrefixFrame configuration) :
    decodePrefix configuration frame =
      UnrolledFFTLayer.decodeVector
        (configuration.arithmetic.boundaryFormat
          configuration.prefixGeometry.completed)
        (unpackNatural configuration frame) := by
  unfold decodePrefix FFTStage.decodeBoundaryFrame
  rw [prefixGeometry_unpack]

/-- Encode a pure fixed-point result in the physical layout consumed by the
final reorderer. -/
def encodeFinalPhysical (configuration : Configuration depth)
    (values : HTFFT.Fixed.Vector depth) : OutputFrame configuration :=
  FFTStage.encodeBoundaryFrame configuration.arithmetic
    configuration.finalGeometry values

/-- Decode the physical frame produced by the rolled suffix. -/
def decodeFinalPhysical (configuration : Configuration depth)
    (frame : OutputFrame configuration) : HTFFT.Fixed.Vector depth :=
  FFTStage.decodeBoundaryFrame configuration.arithmetic
    configuration.finalGeometry frame

/-- Recover the packed logical vector from the final streamed layout without
decoding its fixed-width samples. -/
def unpackFinalPhysical (configuration : Configuration depth)
    (frame : OutputFrame configuration) :
    Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat
          configuration.finalGeometry.completed)).Denote :=
  configuration.finalGeometry.unpack frame

/-- Unpacking an encoded final physical frame recovers its packed logical
vector at the public final format. -/
@[simp] theorem finalGeometry_unpack_encodeFinalPhysical
    (configuration : Configuration depth)
    (values : HTFFT.Fixed.Vector depth) :
    configuration.finalGeometry.unpack
        (encodeFinalPhysical configuration values) =
      UnrolledFFTLayer.encodeVector
        (configuration.arithmetic.boundaryFormat
          configuration.finalGeometry.completed) values := by
  unfold encodeFinalPhysical FFTStage.encodeBoundaryFrame
  exact FFTStage.BoundaryGeometry.unpack_pack _ _

@[simp] theorem unpackFinalPhysical_encodeFinalPhysical
    (configuration : Configuration depth)
    (values : HTFFT.Fixed.Vector depth) :
    unpackFinalPhysical configuration
        (encodeFinalPhysical configuration values) =
      UnrolledFFTLayer.encodeVector
        (configuration.arithmetic.boundaryFormat
          configuration.finalGeometry.completed) values := by
  unfold unpackFinalPhysical
  exact finalGeometry_unpack_encodeFinalPhysical configuration values

/-- Encode a pure fixed-point result in natural external order. -/
def encodeOutput (configuration : Configuration depth)
    (values : HTFFT.Fixed.Vector depth) : OutputFrame configuration :=
  packOutput configuration
    (UnrolledFFTLayer.encodeVector
      (configuration.arithmetic.boundaryFormat
        configuration.finalGeometry.completed) values)

end HTFFT.Silean.FFT
