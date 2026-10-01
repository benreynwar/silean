import HTFFT.Silean.InitialReorder.BankLane.Internal.BankLaneStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.InitialReorder.BankLane
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
   occurrence depth configuration .payloadUnpack,
   occurrence depth configuration .bank,
   occurrence depth configuration .outputRegister])

private theorem childStructuralCertifications (depth : Nat)
    (configuration : Configuration depth) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration child)
  | .trueSource => (Constant.certification .bit true).structural
  | .payloadUnpack =>
      (NamedTupleSplitter.certification
        (InitialReorder.Lane.payloadMap configuration)).structural
  | .bank =>
      (RegisterBank.certification (sampleType configuration)
        (InitialReorder.addressWidth configuration) 1).structural
  | .outputRegister =>
      (Register.certification (sampleType configuration)).structural

theorem structuralCertification (depth : Nat)
    (configuration : Configuration depth) :
    ModuleStructuralCertification (moduleStructure depth configuration) :=
  (completeSchedule depth configuration).certifyComposite
    (structuralChildren depth configuration)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration) (structuralChildren depth configuration)
      (childStructuralCertifications depth configuration))
    (fun _ => rfl)

end HTFFT.Silean.InitialReorder.BankLane
