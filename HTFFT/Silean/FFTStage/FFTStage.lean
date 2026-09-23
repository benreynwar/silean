import HTFFT.Silean.FFTStage.FrameLayout
import HTFFT.Silean.FFTConfiguration
import HTFFT.Silean.UnrolledFFTLayer.UnrolledFFTLayer
import Silean.Authoring.ModulePorts

/-! # One shift-register streaming FFT stage

This file contains only the public boundary and natural framed behavior.  A
complete input frame is decoded through the stage's input stream layout, one
ordinary `HTFFT.Fixed.butterflyLayer` is applied, and the result is encoded in
the next boundary layout.  Shift registers, phase control, twiddle ROMs, and
butterfly instances belong to the separate structural implementation.
-/

namespace HTFFT.Silean.FFTStage

open _root_.Silean
open HTFFT.FixedPoint

/-- Packed complex sample type at one fixed-point boundary. -/
abbrev complexSignalType := UnrolledFFTLayer.complexSignalType

/-- Packed payload carried in one cycle at an arbitrary streamed boundary. -/
abbrev BoundaryData (configuration : FFTConfiguration depth)
    (boundary : BoundaryGeometry depth) :=
  Fin boundary.laneCount →
    (complexSignalType
      (configuration.boundaryFormat boundary.completed)).Denote

/-- Complete packed frame at an arbitrary streamed boundary. -/
abbrev BoundaryFrame (configuration : FFTConfiguration depth)
    (boundary : BoundaryGeometry depth) :=
  boundary.StreamFrame
    (complexSignalType
      (configuration.boundaryFormat boundary.completed)).Denote

/-- Decode a packed streamed boundary into the ordinary logical fixed-point
vector denoted by that boundary. -/
def decodeBoundaryFrame (configuration : FFTConfiguration depth)
    (boundary : BoundaryGeometry depth)
    (frame : BoundaryFrame configuration boundary) : HTFFT.Fixed.Vector depth :=
  UnrolledFFTLayer.decodeVector
    (configuration.boundaryFormat boundary.completed)
    (boundary.unpack frame)

/-- Encode an ordinary logical fixed-point vector at a streamed boundary. -/
def encodeBoundaryFrame (configuration : FFTConfiguration depth)
    (boundary : BoundaryGeometry depth) (values : HTFFT.Fixed.Vector depth) :
    BoundaryFrame configuration boundary :=
  boundary.pack
    (UnrolledFFTLayer.encodeVector
      (configuration.boundaryFormat boundary.completed) values)

/-- Transport one cycle payload between propositionally equal boundaries. -/
def castBoundaryData (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (data : BoundaryData configuration source) :
    BoundaryData configuration target :=
  equal ▸ data

/-- `castBoundaryData` is ordinary equality transport in the boundary-data
family. -/
theorem castBoundaryData_eq_mp
    (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (data : BoundaryData configuration source) :
    castBoundaryData configuration equal data =
      Eq.mp (congrArg (BoundaryData configuration) equal) data := by
  subst target
  rfl

/-- Transport a packed frame between propositionally equal boundary
geometries. -/
def castBoundaryFrame (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (frame : BoundaryFrame configuration source) :
    BoundaryFrame configuration target :=
  fun cycle =>
    castBoundaryData configuration equal
      (frame (Fin.cast
        (congrArg BoundaryGeometry.frameLength equal).symm cycle))

/-- Transporting a complete frame is pointwise payload transport, with the
cycle index transported along the same boundary equality. -/
@[simp] theorem castBoundaryFrame_apply
    (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (frame : BoundaryFrame configuration source)
    (cycle : Fin target.frameLength) :
    castBoundaryFrame configuration equal frame cycle =
      castBoundaryData configuration equal
        (frame (Fin.cast
          (congrArg BoundaryGeometry.frameLength equal).symm cycle)) := by
  rfl

/-- Decoding is invariant under transport between equal boundaries. -/
@[simp] theorem decodeBoundaryFrame_cast
    (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (frame : BoundaryFrame configuration source) :
    decodeBoundaryFrame configuration target
        (castBoundaryFrame configuration equal frame) =
      decodeBoundaryFrame configuration source frame := by
  subst target
  rfl

/-- Encoding commutes with transport between equal streamed boundaries. -/
@[simp] theorem castBoundaryFrame_encodeBoundaryFrame
    (configuration : FFTConfiguration depth)
    {source target : BoundaryGeometry depth} (equal : source = target)
    (values : HTFFT.Fixed.Vector depth) :
    castBoundaryFrame configuration equal
        (encodeBoundaryFrame configuration source values) =
      encodeBoundaryFrame configuration target values := by
  subst target
  rfl

/-- Packing after decoding is the identity on an arbitrary streamed boundary
frame. -/
@[simp] theorem encodeBoundaryFrame_decodeBoundaryFrame
    (configuration : FFTConfiguration depth)
    (boundary : BoundaryGeometry depth)
    (frame : BoundaryFrame configuration boundary) :
    encodeBoundaryFrame configuration boundary
        (decodeBoundaryFrame configuration boundary frame) = frame := by
  unfold encodeBoundaryFrame decodeBoundaryFrame
  rw [UnrolledFFTLayer.encodeVector_decodeVector,
    BoundaryGeometry.pack_unpack]

/-- Packed input payload carried during every cycle of a frame. -/
abbrev InputData (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  BoundaryData configuration geometry.inputBoundary

/-- Packed output payload carried during every cycle of a frame. -/
abbrev OutputData (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  BoundaryData configuration geometry.outputBoundary

/-- Complete streamed input payload, excluding the frame marker. -/
abbrev InputFrame (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  BoundaryFrame configuration geometry.inputBoundary

/-- Complete streamed output payload, excluding the frame marker. -/
abbrev OutputFrame (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  BoundaryFrame configuration geometry.outputBoundary

/-- Decode one physical input frame into the ordinary logical fixed-point
vector at this layer boundary. -/
def decodeInputFrame (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (frame : InputFrame configuration geometry) : HTFFT.Fixed.Vector depth :=
  decodeBoundaryFrame configuration geometry.inputBoundary frame

/-- Encode a logical fixed-point vector in the physical output layout of this
stage. -/
def encodeOutputFrame (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) (values : HTFFT.Fixed.Vector depth) :
    OutputFrame configuration geometry :=
  encodeBoundaryFrame configuration geometry.outputBoundary values

/-- Decode a physical output frame into an ordinary logical fixed-point
vector. -/
def decodeOutputFrame (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (frame : OutputFrame configuration geometry) : HTFFT.Fixed.Vector depth :=
  decodeBoundaryFrame configuration geometry.outputBoundary frame

/-- Decoding an encoded output frame applies only the fixed-width canonical
representative operation to each logical value. -/
theorem decodeOutputFrame_encodeOutputFrame
    (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) (values : HTFFT.Fixed.Vector depth) :
    decodeOutputFrame configuration geometry
        (encodeOutputFrame configuration geometry values) =
      fun index => HTFFT.Butterfly.Fixed.wrapComplex
        (configuration.boundaryFormat geometry.stage.succ) (values index) := by
  rw [decodeOutputFrame, encodeOutputFrame, decodeBoundaryFrame,
    encodeBoundaryFrame,
    BoundaryGeometry.unpack_pack,
    UnrolledFFTLayer.decodeVector_encodeVector]
  funext index
  apply congrArg (fun format =>
    HTFFT.Butterfly.Fixed.wrapComplex format (values index))
  apply congrArg configuration.boundaryFormat
  apply Fin.ext
  rfl

/-- Natural result of one streaming FFT stage. -/
def resultValue (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : InputFrame configuration geometry) : HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.butterflyLayer configuration.fixedConfig table geometry.stage
    (decodeInputFrame configuration geometry input)

/-- The stage result is already canonical at its output width, so encoding and
decoding the expected output frame returns the exact pure result. -/
@[simp] theorem decodeOutputFrame_encode_resultValue
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : InputFrame configuration geometry) :
    decodeOutputFrame configuration geometry
        (encodeOutputFrame configuration geometry
          (resultValue configuration table geometry input)) =
      resultValue configuration table geometry input := by
  rw [decodeOutputFrame, encodeOutputFrame, decodeBoundaryFrame,
    encodeBoundaryFrame,
    BoundaryGeometry.unpack_pack,
    UnrolledFFTLayer.decodeVector_encodeVector]
  exact HTFFT.Fixed.wrapComplex_butterflyLayer
    configuration.fixedConfig table geometry.stage _

module_ports ports (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) where
  input i_first : .bit,
  input i_data : .vector geometry.laneCount
    (complexSignalType
      (configuration.boundaryFormat geometry.stage.castSucc)),
  output o_first : .bit,
  output o_data : .vector geometry.laneCount
    (complexSignalType
      (configuration.boundaryFormat geometry.stage.succ))

/-- Ordinary carried value used when composing this module's input contract
with neighboring framed modules. -/
abbrev InputObservation (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  Bool × InputData configuration geometry

/-- Ordinary carried value used when composing this module's output contract
with neighboring framed modules. -/
abbrev OutputObservation (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  Bool × OutputData configuration geometry

/-- Consecutive stage instances carry exactly the same observation type at
their shared boundary. -/
theorem next_inputObservation_eq_outputObservation
    (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth) :
    InputObservation configuration (geometry.next hasNext) =
      OutputObservation configuration geometry := by
  rfl

/-- Project one input port record to its frame marker and data payload. -/
def inputObservation (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (input : (ports configuration geometry).inputs.Values) :
    InputObservation configuration geometry :=
  (input Input.i_first, input Input.i_data)

/-- Project one output port record to its frame marker and data payload. -/
def outputObservation (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (output : (ports configuration geometry).outputs.Values) :
    OutputObservation configuration geometry :=
  (output Output.o_first, output Output.o_data)

/-- Natural relation on carried observations, independent of port labels. -/
def carriedRelation (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : FramedLatency.Frame geometry.frameLength
      (InputObservation configuration geometry))
    (output : FramedLatency.Frame geometry.frameLength
      (OutputObservation configuration geometry)) : Prop :=
  (fun cycle => (output cycle).2) =
    encodeOutputFrame configuration geometry
      (resultValue configuration table geometry
        (fun cycle => (input cycle).2))

/-- Natural relation between one valid input frame and its delayed output
frame.  Marker timing is supplied separately by `FramedLatency.Holds`. -/
def frameRelation (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : FramedLatency.Frame geometry.frameLength
      (ports configuration geometry).inputs.Values)
    (output : FramedLatency.Frame geometry.frameLength
      (ports configuration geometry).outputs.Values) : Prop :=
  carriedRelation configuration table geometry
    (fun cycle => inputObservation configuration geometry (input cycle))
    (fun cycle => outputObservation configuration geometry (output cycle))

/-- Framed fixed-latency contract for one shift-register streaming FFT layer.

Only complete candidate frames whose first cycle has `i_first = true` and
whose remaining cycles have `i_first = false` constrain the output.  Such a
frame produces the pure fixed-point layer result exactly `latency` cycles
later, with `o_first` marking its first output cycle. -/
def contract (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (latency : Nat) (trace : BoundaryTrace (ports configuration geometry)) : Prop :=
  FramedLatency.Holds geometry.frameLength latency geometry.frameLength_pos
    (fun input : (ports configuration geometry).inputs.Values =>
      (inputObservation configuration geometry input).1 = true)
    (fun output : (ports configuration geometry).outputs.Values =>
      (outputObservation configuration geometry output).1 = true)
    (frameRelation configuration table geometry) trace

/-- Project the public port-record contract to the ordinary `(first, data)`
values used for serial composition with neighboring stages. -/
theorem relates_of_contract
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (latency : Nat) {trace : BoundaryTrace (ports configuration geometry)}
    (holds : contract configuration table geometry latency trace) :
    FramedLatency.Relates geometry.frameLength latency
      geometry.frameLength_pos
      (fun input : InputObservation configuration geometry => input.1 = true)
      (fun output : OutputObservation configuration geometry => output.1 = true)
      (carriedRelation configuration table geometry)
      (trace.inputs.map (inputObservation configuration geometry))
      (trace.outputs.map (outputObservation configuration geometry)) := by
  apply FramedLatency.relates_of_holds_projection
    (inputObservation configuration geometry)
    (outputObservation configuration geometry)
  exact holds

end HTFFT.Silean.FFTStage
