import HTFFT.Silean.FinalReorder.Control.Internal.ControlStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.FinalReorder.Control

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
   occurrence addressWidth .zeroAddress,
   occurrence addressWidth .lastAddress,
   occurrence addressWidth .writeCounter,
   occurrence addressWidth .readCounter,
   occurrence addressWidth .writeSelect,
   occurrence addressWidth .readSelect,
   occurrence addressWidth .writeSplit,
   occurrence addressWidth .lowSelect,
   occurrence addressWidth .lowSplit,
   occurrence addressWidth .highSelect,
   occurrence addressWidth .highSplit,
   occurrence addressWidth .lowInvert,
   occurrence addressWidth .writeAddress0,
   occurrence addressWidth .writeAddress1,
   occurrence addressWidth .bypass])

private theorem childStructuralCertifications (addressWidth : Nat) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren addressWidth child)
  | .trueSource => (Constant.certification .bit true).structural
  | .zeroAddress =>
      (Constant.certification (.vector addressWidth .bit)
        (zeroAddress addressWidth)).structural
  | .lastAddress =>
      (Constant.certification (.vector addressWidth .bit)
        (lastAddress addressWidth)).structural
  | .writeCounter | .readCounter =>
      (EnabledResetCounter.certification addressWidth
        (oneAddress addressWidth)).structural
  | .writeSelect | .readSelect =>
      (Mux.certification (.vector addressWidth .bit)).structural
  | .writeSplit =>
      (Internal.addressSplitter addressWidth).structuralCertification
  | .lowSelect =>
      (VectorLayout.certification addressWidth 1
        (Internal.lowBitLayout addressWidth)).structural
  | .lowSplit => Internal.oneBitSplitter.structuralCertification
  | .highSelect =>
      (VectorLayout.certification addressWidth 1
        (Internal.highBitLayout addressWidth)).structural
  | .highSplit => Internal.oneBitSplitter.structuralCertification
  | .lowInvert =>
      Primitives.notCertified.structuralCertification
  | .writeAddress0 | .writeAddress1 =>
      (Internal.addressCombiner addressWidth).structuralCertification
  | .bypass =>
      (Equality.certification (.vector addressWidth .bit)).structural

theorem Internal.structuralCertification (addressWidth : Nat) :
    ModuleStructuralCertification (moduleStructure addressWidth) :=
  (completeSchedule addressWidth).certifyComposite
    (structuralChildren addressWidth)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body addressWidth) (structuralChildren addressWidth)
      (childStructuralCertifications addressWidth))
    (fun _ => rfl)

end HTFFT.Silean.FinalReorder.Control
