import HTFFT.Silean.FinalReorder.Internal.FinalReorderStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.FinalReorder
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules (depth : Nat)
    (configuration : Configuration depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration)

private abbrev occurrence (depth : Nat)
    (configuration : Configuration depth) (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration) (wholeRules depth configuration) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule (depth : Nat)
    (configuration : Configuration depth)
    for body depth configuration with wholeRules depth configuration := from (
  [occurrence depth configuration .trueSource,
   occurrence depth configuration .markerDelay,
   occurrence depth configuration .control,
   occurrence depth configuration .inputSplit,
   occurrence depth configuration .lowerCombine,
   occurrence depth configuration .upperCombine,
   occurrence depth configuration .bank0Write,
   occurrence depth configuration .bank1Write,
   occurrence depth configuration .bank0,
   occurrence depth configuration .bank1,
   occurrence depth configuration .bank1Bypass,
   occurrence depth configuration .lowerOutput,
   occurrence depth configuration .upperOutput,
   occurrence depth configuration .lowerSplit,
   occurrence depth configuration .upperSplit,
   occurrence depth configuration .outputCombine])

private theorem childStructuralCertifications (depth : Nat)
    (configuration : Configuration depth) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration child)
  | .trueSource => (Constant.certification .bit true).structural
  | .control => FinalReorder.Control.structuralCertification
      (Internal.addressWidth configuration)
  | .inputSplit =>
      (Internal.inputSplitter configuration).structuralCertification
  | .lowerCombine | .upperCombine =>
      (Internal.halfCombiner configuration).structuralCertification
  | .bank0Write | .bank1Write | .bank1Bypass |
      .lowerOutput | .upperOutput =>
      (Mux.certification (Internal.halfVectorType configuration)).structural
  | .bank0 | .bank1 =>
      (RegisterBank.certification (Internal.halfVectorType configuration)
        (Internal.addressWidth configuration) 1).structural
  | .lowerSplit | .upperSplit =>
      (Internal.halfSplitter configuration).structuralCertification
  | .outputCombine =>
      (Internal.outputCombiner configuration).structuralCertification
  | .markerDelay => ShiftRegister.structuralCertification .bit
      configuration.finalReorderLatency
      (Configuration.finalReorderLatency_pos configuration)

theorem Internal.structuralCertification (depth : Nat)
    (configuration : Configuration depth) :
    ModuleStructuralCertification (moduleStructure depth configuration) :=
  (completeSchedule depth configuration).certifyComposite
    (structuralChildren depth configuration)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration) (structuralChildren depth configuration)
      (childStructuralCertifications depth configuration))
    (fun _ => rfl)

end HTFFT.Silean.FinalReorder
