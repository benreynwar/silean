import HTFFT.Silean.InitialReorder.Internal.InitialReorderStructure
import Silean.Authoring.ModuleRuleSchedules

/-! A readable complete dependency order for the concrete initial reorder.

The indexed lane modules are represented as ordinary mapped lists here. The
schedule elaborator checks both dependency availability and complete coverage;
the circuit itself does not contain this proof-only ordering. -/

namespace HTFFT.Silean.InitialReorder
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev wholeRules (depth : Nat)
    (configuration : Configuration depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration)

private abbrev occurrence (depth : Nat)
    (configuration : Configuration depth)
    (child : Instance configuration) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration) (wholeRules depth configuration) :=
  ⟨child, .apply⟩

private def laneOccurrences (depth : Nat)
    (configuration : Configuration depth)
    (child : Fin (Internal.laneCount configuration) →
      Instance configuration) :
    List (ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration) (wholeRules depth configuration)) :=
  (Enumeration.fin (Internal.laneCount configuration)).values.map fun lane =>
    occurrence depth configuration (child lane)

private def completeOrder (depth : Nat)
    (configuration : Configuration depth) :
    List (ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration) (wholeRules depth configuration)) :=
  [occurrence depth configuration .trueSource,
   occurrence depth configuration .control,
   occurrence depth configuration .laneRotation,
   occurrence depth configuration .preRotation,
   occurrence depth configuration .preSplit] ++
  laneOccurrences depth configuration .addressPayload ++
  [occurrence depth configuration .payloadCombine,
   occurrence depth configuration .preBarrel,
   occurrence depth configuration .payloadSplit,
   occurrence depth configuration .readCycleAlign,
   occurrence depth configuration .readOrientationAlign,
   occurrence depth configuration .readOrientationInvert,
   occurrence depth configuration .readRotationAlign,
   occurrence depth configuration .readPreRotation] ++
  laneOccurrences depth configuration .readAddressPayload ++
  [occurrence depth configuration .readAddressCombine,
   occurrence depth configuration .readPreBarrel,
   occurrence depth configuration .readAddressSplit] ++
  laneOccurrences depth configuration .bank ++
  [occurrence depth configuration .bankCombine,
   occurrence depth configuration .postRotationAlign,
   occurrence depth configuration .postBarrel,
   occurrence depth configuration .markerAlign]

set_option maxHeartbeats 1000000 in
module_complete_schedule completeSchedule (depth : Nat)
    (configuration : Configuration depth)
    for body depth configuration with wholeRules depth configuration := from (
  completeOrder depth configuration)

noncomputable def Internal.completeSchedule (depth : Nat)
    (configuration : Configuration depth) :
    ModuleStructuralCertification.Layer.ScheduleDerivation.DerivedCompleteSchedule
      (body depth configuration) (wholeRules depth configuration) :=
  HTFFT.Silean.InitialReorder.completeSchedule depth configuration

end HTFFT.Silean.InitialReorder
