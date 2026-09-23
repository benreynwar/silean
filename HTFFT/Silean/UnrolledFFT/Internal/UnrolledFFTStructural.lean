import HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent certification of the natural-order FFT wrapper. -/

namespace HTFFT.Silean.UnrolledFFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration table)

private abbrev occurrence
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration table)
      (wholeRules depth configuration table) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    for body depth configuration table
    with wholeRules depth configuration table := from (
  [occurrence depth configuration table .reorder,
   occurrence depth configuration table .network])

private theorem childStructuralCertifications
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren depth configuration table child)
  | .reorder =>
      (VectorReindex.certification
        (UnrolledFFTLayer.complexSignalType
          (configuration.boundaryFormat 0))
        (2 ^ depth) (2 ^ depth) HTFFT.Exact.bitReverseIndex).structural
  | .network =>
      UnrolledFFTNetwork.structuralCertification configuration table

/-- The natural-order wrapper has exactly one structural solution for every
input and physical state. -/
theorem Internal.structuralCertification
    (depth : Nat) (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table) :=
  (completeSchedule depth configuration table).certifyComposite
    (structuralChildren depth configuration table)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration table)
      (structuralChildren depth configuration table)
      (childStructuralCertifications depth configuration table))
    (fun _ => rfl)

end HTFFT.Silean.UnrolledFFT
