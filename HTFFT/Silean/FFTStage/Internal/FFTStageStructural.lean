import HTFFT.Silean.FFTStage.Internal.FFTStageStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent certification of the generic rolled FFT stage. -/

namespace HTFFT.Silean.FFTStage

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules (depth : Nat)
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration table geometry pipeline twiddleDefinitionName)

private abbrev occurrence (depth : Nat)
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) (child : Instance geometry) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration table geometry pipeline twiddleDefinitionName)
      (wholeRules depth configuration table geometry pipeline
        twiddleDefinitionName) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    for body depth configuration table geometry pipeline twiddleDefinitionName
    with wholeRules depth configuration table geometry pipeline
      twiddleDefinitionName := from (
  [occurrence depth configuration table geometry pipeline twiddleDefinitionName
      .inputSplit,
   occurrence depth configuration table geometry pipeline twiddleDefinitionName
      .control] ++
  (Enumeration.fin (Internal.butterflyCount geometry)).values.map
    (fun lane => occurrence depth configuration table geometry pipeline
      twiddleDefinitionName (.lane lane)) ++
  [occurrence depth configuration table geometry pipeline twiddleDefinitionName
      .outputCombine,
   occurrence depth configuration table geometry pipeline twiddleDefinitionName
      .markerAlign])

private theorem childStructuralCertifications
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration table geometry pipeline
        twiddleDefinitionName child)
  | .inputSplit =>
      (Internal.inputSplitter configuration geometry).structuralCertification
  | .control => FFTStageControl.Internal.structuralCertification
      (Internal.phaseExponent geometry)
  | .lane lane => FFTStageLane.Internal.structuralCertification
      (Internal.dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (Internal.phaseExponent geometry) (Internal.phaseWidth geometry)
      (Internal.laneAddressWidth geometry) lane.val twiddleDefinitionName
      (Internal.twiddleValues configuration table geometry) pipeline
  | .outputCombine =>
      (Internal.outputCombiner configuration geometry).structuralCertification
  | .markerAlign => OptionalShiftRegister.structuralCertification .bit
      pipeline.latency

/-- The complete generic stage has exactly one structural solution for every
input and physical state. -/
theorem Internal.structuralCertification
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table geometry pipeline
        twiddleDefinitionName) :=
  (completeSchedule depth configuration table geometry pipeline
    twiddleDefinitionName).certifyComposite
      (structuralChildren depth configuration table geometry pipeline
        twiddleDefinitionName)
      (ModuleStructuralCertification.Layer.wholeCertifiedChildren
        (body depth configuration table geometry pipeline twiddleDefinitionName)
        (structuralChildren depth configuration table geometry pipeline
          twiddleDefinitionName)
        (childStructuralCertifications depth configuration table geometry
          pipeline twiddleDefinitionName))
      (fun _ => rfl)

end HTFFT.Silean.FFTStage
