import Silean.Semantics.FramedLatency
import Mathlib.Tactic

namespace SileanTests.FramedLatency

open Silean

#check FramedLatency.window
#check FramedLatency.window_map
#check FramedLatency.Starts
#check FramedLatency.not_starts_of_early_marker
#check FramedLatency.relates_of_holds_projection
#check FramedLatency.holds_of_relates_projection
#check FramedLatency.relation_at
#check FramedLatency.mono
#check FramedLatency.serial
#check FramedLatency.computes_serial
#check FramedLatency.computes_id
#check FramedLatency.computes_map_inputs
#check FramedLatency.computes_map_outputs
#check FramedLatency.computes_of_components
#check FramedLatency.computes_of_payload_relation

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

end SileanTests.FramedLatency
