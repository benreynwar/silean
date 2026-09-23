import HTFFT.Silean.FFTStage

assert_not_imported HTFFT.Silean.FFTStage.Internal.FFTStageStructure
assert_not_imported HTFFT.Silean.FFTStage.Internal.FFTStageVerification

namespace HTFFTTests.FFTStageContract

open Silean
open HTFFT
open HTFFT.Silean

#check FramedLatency.Starts
#check FramedLatency.not_starts_of_early_marker
#check FramedLatency.relates_of_holds_projection
#check FramedLatency.serial
#check FramedLatency.computes_serial

#check FFTStage.BoundaryGeometry.layout
#check FFTStage.BoundaryGeometry.layout_val
#check FFTStage.BoundaryGeometry.unpack_pack
#check FFTStage.BoundaryGeometry.pack_unpack
#check FFTStage.Geometry.next_inputBoundary
#check FFTStage.next_inputObservation_eq_outputObservation

#check FFTStage.resultValue
#check FFTStage.decodeOutputFrame_encode_resultValue
#check FFTStage.frameRelation
#check FFTStage.contract
#check FFTStage.relates_of_contract

/-- Four lanes carrying a sixteen-point frame.  Stage two is the first
streaming layer after a two-layer unrolled prefix. -/
def stageTwo : FFTStage.Geometry 4 where
  laneDepth := 2
  stage := ⟨2, by decide⟩
  laneDepth_pos := by decide
  laneDepth_le_stage := by decide

def stageThree : FFTStage.Geometry 4 :=
  stageTwo.next (by decide)

def layoutRows (geometry : FFTStage.BoundaryGeometry depth) :
    List (List Nat) :=
  List.ofFn fun cycle : Fin geometry.frameLength =>
    List.ofFn fun lane : Fin geometry.laneCount =>
      (geometry.layout (cycle, lane)).val

-- Before the first streaming layer, cycles and lanes are ordinary
-- cycle-major coordinates.
#guard layoutRows stageTwo.inputBoundary ==
  [[0, 1, 2, 3], [4, 5, 6, 7],
   [8, 9, 10, 11], [12, 13, 14, 15]]

-- The first rolled layer exchanges logical bit two with the high lane bit.
#guard layoutRows stageTwo.outputBoundary ==
  [[0, 1, 4, 5], [2, 3, 6, 7],
   [8, 9, 12, 13], [10, 11, 14, 15]]

-- The next stage consumes exactly that layout and moves logical bit three
-- into the high lane bit at its output.
#guard layoutRows stageThree.inputBoundary ==
  [[0, 1, 4, 5], [2, 3, 6, 7],
   [8, 9, 12, 13], [10, 11, 14, 15]]

#guard layoutRows stageThree.outputBoundary ==
  [[0, 1, 8, 9], [2, 3, 10, 11],
   [4, 5, 12, 13], [6, 7, 14, 15]]

private def markedFrame (secondMarker : Bool) :
    FramedLatency.Frame 4 Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => secondMarker
  | _ => false

example : FramedLatency.Starts (by omega) (· = true) (markedFrame false) := by
  constructor
  · rfl
  · intro offset nonzero
    fin_cases offset <;> simp_all [markedFrame]

example : ¬ FramedLatency.Starts (by omega) (· = true) (markedFrame true) := by
  apply FramedLatency.not_starts_of_early_marker
    (offset := ⟨1, by decide⟩) (by decide)
  rfl

end HTFFTTests.FFTStageContract
