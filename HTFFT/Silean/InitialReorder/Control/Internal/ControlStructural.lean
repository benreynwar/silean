import HTFFT.Silean.InitialReorder.Control.Internal.ControlStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.InitialReorder.Control

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules (addressWidth : Nat) :=
  ModuleStructuralCertification.Layer.wholeChildRules (body addressWidth)

private abbrev occurrence (addressWidth : Nat) (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence (body addressWidth)
      (wholeRules addressWidth) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule (addressWidth : Nat)
    for body addressWidth with wholeRules addressWidth := from (
  [occurrence addressWidth .trueSource,
   occurrence addressWidth .falseSource,
   occurrence addressWidth .zeroAddress,
   occurrence addressWidth .lastAddress,
   occurrence addressWidth .addressCounter,
   occurrence addressWidth .addressSelect,
   occurrence addressWidth .atLast,
   occurrence addressWidth .orientationCounter,
   occurrence addressWidth .orientationSplit])

private theorem childStructuralCertifications (addressWidth : Nat) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren addressWidth child)
  | .trueSource =>
      (Constant.certification .bit true).structural
  | .falseSource =>
      (Constant.certification .bit false).structural
  | .zeroAddress =>
      (Constant.certification (.vector addressWidth .bit)
        (zeroAddress addressWidth)).structural
  | .lastAddress =>
      (Constant.certification (.vector addressWidth .bit)
        (lastAddress addressWidth)).structural
  | .addressCounter =>
      (EnabledResetCounter.certification addressWidth
        (oneAddress addressWidth)).structural
  | .addressSelect =>
      (Mux.certification (.vector addressWidth .bit)).structural
  | .atLast =>
      (Equality.certification (.vector addressWidth .bit)).structural
  | .orientationCounter =>
      (EnabledResetCounter.certification 1
        (Internal.orientationValue false)).structural
  | .orientationSplit =>
      Internal.orientationSplitter.structuralCertification

theorem Internal.structuralCertification (addressWidth : Nat) :
    ModuleStructuralCertification (moduleStructure addressWidth) :=
  (completeSchedule addressWidth).certifyComposite
    (structuralChildren addressWidth)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body addressWidth) (structuralChildren addressWidth)
      (childStructuralCertifications addressWidth))
    (fun _ => rfl)

end HTFFT.Silean.InitialReorder.Control
