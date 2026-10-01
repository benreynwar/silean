import HTFFT.Silean.FFT.Internal.FFTStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent structural certification of the complete concrete
FFT hierarchy. -/

namespace HTFFT.Silean.FFT

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
      (body depth configuration)
      (wholeRules depth configuration) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule
    (depth : Nat) (configuration : Configuration depth)
    for body depth configuration
      with wholeRules depth configuration := from (
  [occurrence depth configuration .initialReorder,
   occurrence depth configuration .unrolled,
   occurrence depth configuration .unrolledFirstDelay,
   occurrence depth configuration .stageChain,
   occurrence depth configuration .finalReorder])

private theorem childStructuralCertifications
    (depth : Nat) (configuration : Configuration depth) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration child)
  | .initialReorder =>
      InitialReorder.structuralCertification depth configuration
  | .unrolled =>
      UnrolledFFTNetwork.structuralCertification configuration.unrolled
        configuration.prefixTable
  | .unrolledFirstDelay =>
      OptionalShiftRegister.structuralCertification .bit
        configuration.unrolled.networkLatency
  | .stageChain =>
      FFTStageChain.structuralCertification configuration
  | .finalReorder =>
      FinalReorder.structuralCertification depth configuration

theorem Internal.structuralCertification
    (depth : Nat) (configuration : Configuration depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration) :=
  (completeSchedule depth configuration).certifyComposite
    (structuralChildren depth configuration)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration)
      (structuralChildren depth configuration)
      (childStructuralCertifications depth configuration))
    (fun _ => rfl)

end HTFFT.Silean.FFT
