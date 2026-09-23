import HTFFT.Silean.FFTStage.FFTStage

/-! # Semantic composition of streaming FFT stages

These theorems validate the public framed contract independently of the
structural implementation.  Consecutive geometries use the same physical
boundary layout, so decoding one stage's output is exactly the decoding used
by the next stage's input.  Consequently serial contract composition applies
the corresponding sequence of ordinary fixed-point butterfly layers.
-/

namespace HTFFT.Silean.FFTStage

open _root_.Silean

/-- Consecutive stages interpret their shared physical frame identically. -/
theorem decodeInputFrame_next_eq_decodeOutputFrame
    (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth)
    (frame : OutputFrame configuration geometry) :
    decodeInputFrame configuration (geometry.next hasNext) frame =
      decodeOutputFrame configuration geometry frame := by
  rfl

/-- Feeding the encoded result of one stage to its successor recovers exactly
the canonical fixed-point vector produced by the first stage. -/
@[simp] theorem decodeInputFrame_next_encode_resultValue
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth)
    (input : InputFrame configuration geometry) :
    decodeInputFrame configuration (geometry.next hasNext)
        (encodeOutputFrame configuration geometry
          (resultValue configuration table geometry input)) =
      resultValue configuration table geometry input := by
  rw [decodeInputFrame_next_eq_decodeOutputFrame]
  exact decodeOutputFrame_encode_resultValue configuration table geometry input

/-- Two consecutive natural stage transformations are exactly two ordinary
fixed-point butterfly layers. -/
theorem resultValue_next_encode_resultValue
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth)
    (input : InputFrame configuration geometry) :
    resultValue configuration table (geometry.next hasNext)
        (encodeOutputFrame configuration geometry
          (resultValue configuration table geometry input)) =
      HTFFT.Fixed.butterflyLayer configuration.fixedConfig table
        (geometry.next hasNext).stage
        (resultValue configuration table geometry input) := by
  change HTFFT.Fixed.butterflyLayer configuration.fixedConfig table
      (geometry.next hasNext).stage
      (decodeInputFrame configuration (geometry.next hasNext)
        (encodeOutputFrame configuration geometry
          (resultValue configuration table geometry input))) = _
  rw [decodeInputFrame_next_encode_resultValue]

/-- Frame-level composition of two neighboring public relations collapses to
the corresponding two fixed-point layers. -/
theorem carriedRelation_comp_next_iff
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth)
    (input : FramedLatency.Frame geometry.frameLength
      (InputObservation configuration geometry))
    (output : FramedLatency.Frame geometry.frameLength
      (OutputObservation configuration (geometry.next hasNext))) :
    FramedLatency.Comp
        (carriedRelation configuration table geometry)
        (carriedRelation configuration table (geometry.next hasNext))
        input output ↔
      (fun cycle => (output cycle).2) =
        encodeOutputFrame configuration (geometry.next hasNext)
          (HTFFT.Fixed.butterflyLayer configuration.fixedConfig table
            (geometry.next hasNext).stage
            (resultValue configuration table geometry
              (fun cycle => (input cycle).2))) := by
  constructor
  · rintro ⟨middle, left, right⟩
    let inputData : InputFrame configuration geometry :=
      fun cycle => (input cycle).2
    let middleData : OutputFrame configuration geometry :=
      fun cycle => (middle cycle).2
    let outputData : OutputFrame configuration (geometry.next hasNext) :=
      fun cycle => (output cycle).2
    change middleData = encodeOutputFrame configuration geometry
      (resultValue configuration table geometry inputData) at left
    change outputData = encodeOutputFrame configuration (geometry.next hasNext)
      (resultValue configuration table (geometry.next hasNext) middleData) at right
    change outputData = encodeOutputFrame configuration (geometry.next hasNext)
      (HTFFT.Fixed.butterflyLayer configuration.fixedConfig table
        (geometry.next hasNext).stage
        (resultValue configuration table geometry inputData))
    calc
      outputData = encodeOutputFrame configuration (geometry.next hasNext)
          (resultValue configuration table (geometry.next hasNext)
            middleData) := right
      _ = encodeOutputFrame configuration (geometry.next hasNext)
          (resultValue configuration table (geometry.next hasNext)
            (encodeOutputFrame configuration geometry
              (resultValue configuration table geometry inputData))) := by
            rw [left]
      _ = _ := by rw [resultValue_next_encode_resultValue]
  · intro equal
    let inputData : InputFrame configuration geometry :=
      fun cycle => (input cycle).2
    let middleData : OutputFrame configuration geometry :=
      encodeOutputFrame configuration geometry
        (resultValue configuration table geometry inputData)
    let middle : FramedLatency.Frame geometry.frameLength
        (OutputObservation configuration geometry) :=
      fun cycle => (cycle.val = 0, middleData cycle)
    refine ⟨middle, ?_, ?_⟩
    · change middleData = encodeOutputFrame configuration geometry
        (resultValue configuration table geometry inputData)
      rfl
    · change (fun cycle => (output cycle).2) =
        encodeOutputFrame configuration (geometry.next hasNext)
          (resultValue configuration table (geometry.next hasNext) middleData)
      calc
        (fun cycle => (output cycle).2) =
            encodeOutputFrame configuration (geometry.next hasNext)
              (HTFFT.Fixed.butterflyLayer configuration.fixedConfig table
                (geometry.next hasNext).stage
                (resultValue configuration table geometry inputData)) := equal
        _ = encodeOutputFrame configuration (geometry.next hasNext)
            (resultValue configuration table (geometry.next hasNext)
              middleData) := by
                symm
                exact congrArg (encodeOutputFrame configuration
                  (geometry.next hasNext))
                  (resultValue_next_encode_resultValue configuration table
                    geometry hasNext inputData)

end HTFFT.Silean.FFTStage
