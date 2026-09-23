import HTFFT.Silean.UnrolledFFTLayer.Internal.UnrolledFFTLayerStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent certification of the generic layer hierarchy. -/

namespace HTFFT.Silean.UnrolledFFTLayer

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration table stage)

private abbrev occurrence
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (child : Instance depth stage) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration table stage)
      (wholeRules depth configuration table stage) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    for body depth configuration table stage
    with wholeRules depth configuration table stage := from (
  [occurrence depth configuration table stage .inputSplit,
   occurrence depth configuration table stage .twiddleTable,
   occurrence depth configuration table stage .twiddleSplit] ++
  (Internal.butterflyEnumeration depth stage).values.map
    (fun index => occurrence depth configuration table stage
      (.butterfly index)) ++
  [occurrence depth configuration table stage .outputCombine])

private theorem childStructuralCertifications
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren depth configuration table stage child)
  | .inputSplit =>
      (Internal.inputSplitter configuration stage).structuralCertification
  | .twiddleTable =>
      (Constant.certification
        (Internal.twiddleTableType configuration stage)
        (Internal.twiddleValues configuration table stage)).structural
  | .twiddleSplit =>
      (Internal.twiddleSplitter configuration stage).structuralCertification
  | .butterfly _ =>
      PipelinedFixedButterfly.structuralCertification
        (configuration.boundaryFormat stage.castSucc)
        (configuration.twiddleFormat stage)
        (configuration.butterflyPipeline stage)
  | .outputCombine =>
      (Internal.outputCombiner configuration stage).structuralCertification

/-- The complete generic layer has exactly one structural solution for every
input and physical state, independently of its arithmetic contract. -/
theorem Internal.structuralCertification
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table stage) :=
  (completeSchedule depth configuration table stage).certifyComposite
    (structuralChildren depth configuration table stage)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration table stage)
      (structuralChildren depth configuration table stage)
      (childStructuralCertifications depth configuration table stage))
    (fun _ => rfl)

end HTFFT.Silean.UnrolledFFTLayer
