import Silean.Authoring.ModuleRuleSchedules
import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyStructure

/-! Contract-independent certification of the complete complex multiplier
hierarchy. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body leftWidth rightWidth discardedWidth multiplierLatency
      registerBeforeRounding)

private abbrev realRealOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding) :=
  ⟨.realReal, .apply⟩

private abbrev imagImagOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.imagImag, .apply⟩

private abbrev realImagOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.realImag, .apply⟩

private abbrev imagRealOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.imagReal, .apply⟩

private abbrev realNumeratorOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.realNumerator, .apply⟩

private abbrev imagNumeratorOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.imagNumerator, .apply⟩

private abbrev numeratorCombineOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.numeratorCombine, .apply⟩

private abbrev numeratorDelayOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.numeratorDelay, .apply⟩

private abbrev numeratorSplitOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.numeratorSplit, .apply⟩

private abbrev realRoundInputOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.realRoundInput, .apply⟩

private abbrev imagRoundInputOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.imagRoundInput, .apply⟩

private abbrev realRoundOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.realRound, .apply⟩

private abbrev imagRoundOccurrence
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding) :=
  ⟨.imagRound, .apply⟩

module_complete_schedule completeSchedule
    (leftWidth : Nat) (rightWidth : Nat)
    (discardedWidth : Nat) (multiplierLatency : Nat)
    (registerBeforeRounding : Bool)
    for body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding
    with wholeRules leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding := from (
  [realRealOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   imagImagOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   realImagOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   imagRealOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   realNumeratorOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   imagNumeratorOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   numeratorCombineOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   numeratorDelayOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   numeratorSplitOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   realRoundInputOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   imagRoundInputOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   realRoundOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding,
   imagRoundOccurrence leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding])

private theorem childStructuralCertifications
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren leftWidth rightWidth discardedWidth multiplierLatency
          registerBeforeRounding child)
  | .realReal | .imagImag | .realImag | .imagReal =>
      PipelinedSignedMultiply.structuralCertification
        leftWidth rightWidth multiplierLatency
  | .realNumerator =>
      (Sub.certification
        (productWidth leftWidth rightWidth)
        (productWidth leftWidth rightWidth) true true true).structural
  | .imagNumerator =>
      (Add.certification
        (productWidth leftWidth rightWidth)
        (productWidth leftWidth rightWidth) true true true).structural
  | .numeratorCombine =>
      (Internal.numeratorSplitter leftWidth rightWidth).combiner.structuralCertification
  | .numeratorDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector 2 (.vector (numeratorWidth leftWidth rightWidth) .bit))
        (Bool.toNat registerBeforeRounding)
  | .numeratorSplit =>
      (Internal.numeratorSplitter leftWidth rightWidth).structuralCertification
  | .realRoundInput | .imagRoundInput =>
      (VectorLayout.certification
        (numeratorWidth leftWidth rightWidth)
        (Internal.roundInputWidth leftWidth rightWidth discardedWidth)
        (Internal.roundInputLayout leftWidth rightWidth discardedWidth)).structural
  | .realRound | .imagRound =>
      (SignedRoundShift.certification
        (resultWidth leftWidth rightWidth discardedWidth)
        (Internal.effectiveDiscard
          leftWidth rightWidth discardedWidth)).structural

/-- The structural hierarchy has exactly one solution for every input and
physical state, independently of its trace contract. -/
theorem Internal.structuralCertification
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool) :
    ModuleStructuralCertification
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding) :=
  (completeSchedule leftWidth rightWidth discardedWidth multiplierLatency
      registerBeforeRounding).certifyComposite
    (structuralChildren leftWidth rightWidth discardedWidth multiplierLatency
      registerBeforeRounding)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body leftWidth rightWidth discardedWidth multiplierLatency registerBeforeRounding)
      (structuralChildren leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)
      (childStructuralCertifications
        leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding))
    (fun _ => rfl)

end HTFFT.Silean.PipelinedSignedComplexMultiply
