import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.FFTStageControl

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules (phaseExponent : Nat) :=
  ModuleStructuralCertification.Layer.wholeChildRules (body phaseExponent)

private abbrev occurrence (phaseExponent : Nat)
    (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence (body phaseExponent)
      (wholeRules phaseExponent) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule (phaseExponent : Nat)
    for body phaseExponent with wholeRules phaseExponent := from (
  [occurrence phaseExponent .trueSource,
   occurrence phaseExponent .phaseZero,
   occurrence phaseExponent .inputPhaseCounter,
   occurrence phaseExponent .inputPhaseSelect,
   occurrence phaseExponent .inputPhaseSplit,
   occurrence phaseExponent .firstHalf,
   occurrence phaseExponent .markerDelay,
   occurrence phaseExponent .outputPhaseCounter,
   occurrence phaseExponent .outputPhaseSelect])

private theorem childStructuralCertifications (phaseExponent : Nat) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren phaseExponent child)
  | .trueSource => (Primitives.constantCertified true).structuralCertification
  | .phaseZero =>
      (Constant.certification
        (.vector (Internal.phaseWidth phaseExponent) .bit)
        (Internal.phaseZero phaseExponent)).structural
  | .inputPhaseCounter =>
      (EnabledResetCounter.certification (Internal.phaseWidth phaseExponent)
        (Internal.phaseOne phaseExponent)).structural
  | .inputPhaseSelect =>
      (Mux.certification
        (.vector (Internal.phaseWidth phaseExponent) .bit)).structural
  | .inputPhaseSplit =>
      (Internal.phaseSplitter phaseExponent).structuralCertification
  | .firstHalf => Primitives.notCertified.structuralCertification
  | .markerDelay => ShiftRegister.structuralCertification .bit
      (2 ^ phaseExponent) (Nat.two_pow_pos phaseExponent)
  | .outputPhaseCounter =>
      (EnabledResetCounter.certification (Internal.phaseWidth phaseExponent)
        (Internal.phaseOne phaseExponent)).structural
  | .outputPhaseSelect =>
      (Mux.certification
        (.vector (Internal.phaseWidth phaseExponent) .bit)).structural

theorem Internal.structuralCertification (phaseExponent : Nat) :
    ModuleStructuralCertification (moduleStructure phaseExponent) :=
  (completeSchedule phaseExponent).certifyComposite
    (structuralChildren phaseExponent)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body phaseExponent) (structuralChildren phaseExponent)
      (childStructuralCertifications phaseExponent))
    (fun _ => rfl)

end HTFFT.Silean.FFTStageControl
