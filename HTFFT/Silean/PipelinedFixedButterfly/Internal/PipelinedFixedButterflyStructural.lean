import HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent certification of the butterfly hierarchy. -/

namespace HTFFT.Silean.PipelinedFixedButterfly

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs)

private abbrev occurrence
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
        registerInputs multiplierLatency registerBeforeRounding registerProduct
        registerOutputs)
      (wholeRules dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule
    (dataWidth : Nat) (dataFractionalBits : Nat)
    (twiddleWidth : Nat) (twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding : Bool) (registerProduct : Bool)
    (registerOutputs : Bool)
    for body dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs
    with wholeRules dataWidth dataFractionalBits twiddleWidth
      twiddleFractionalBits registerInputs multiplierLatency
      registerBeforeRounding registerProduct registerOutputs := from (
  [occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .aInputDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .bInputDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .twiddleInputDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .bSplit,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .twiddleSplit,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .product,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .productRealNarrow,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .productImagNarrow,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .productCombine,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .productDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .productSplit,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .aAlignDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .aSplit,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .upperReal,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .upperImag,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .lowerReal,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .lowerImag,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .upperCombine,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .lowerCombine,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .upperOutputDelay,
   occurrence dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
      registerInputs multiplierLatency registerBeforeRounding registerProduct
      registerOutputs .lowerOutputDelay])

private theorem childStructuralCertifications
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren dataWidth dataFractionalBits twiddleWidth
          twiddleFractionalBits registerInputs multiplierLatency
          registerBeforeRounding registerProduct registerOutputs child)
  | .aInputDelay | .bInputDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector (dataWidth + dataWidth) .bit)
        (Bool.toNat registerInputs)
  | .twiddleInputDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector (twiddleWidth + twiddleWidth) .bit)
        (Bool.toNat registerInputs)
  | .bSplit | .aSplit | .productSplit =>
      (VectorSplit.certification .bit dataWidth dataWidth).structural
  | .twiddleSplit =>
      (VectorSplit.certification .bit twiddleWidth twiddleWidth).structural
  | .product =>
      PipelinedSignedComplexMultiply.structuralCertification
        dataWidth twiddleWidth twiddleFractionalBits
        { multiplierLatency, registerBeforeRounding }
  | .productRealNarrow | .productImagNarrow =>
      (VectorLayout.certification
        (PipelinedSignedComplexMultiply.resultWidth
          dataWidth twiddleWidth twiddleFractionalBits)
        dataWidth
        (VectorLayout.extensionLayout true
          (PipelinedSignedComplexMultiply.resultWidth
            dataWidth twiddleWidth twiddleFractionalBits)
          dataWidth)).structural
  | .productCombine =>
      (VectorConcat.certification .bit dataWidth dataWidth).structural
  | .productDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector (dataWidth + dataWidth) .bit)
        (Bool.toNat registerProduct)
  | .aAlignDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector (dataWidth + dataWidth) .bit)
        (multiplierLatency + Bool.toNat registerBeforeRounding +
          Bool.toNat registerProduct)
  | .upperReal | .upperImag =>
      (Add.certification dataWidth dataWidth true true true).structural
  | .lowerReal | .lowerImag =>
      (Sub.certification dataWidth dataWidth true true true).structural
  | .upperCombine | .lowerCombine =>
      (VectorConcat.certification .bit
        (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)
        (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)).structural
  | .upperOutputDelay | .lowerOutputDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector
          (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩ +
            outputComponentWidth ⟨dataWidth, dataFractionalBits⟩) .bit)
        (Bool.toNat registerOutputs)

/-- The complete hierarchy has a unique solution for every input and physical
state, independently of the arithmetic trace contract. -/
theorem Internal.structuralCertification
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool) :
    ModuleStructuralCertification
      (moduleStructure dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs) :=
  (completeSchedule dataWidth dataFractionalBits twiddleWidth
      twiddleFractionalBits registerInputs multiplierLatency
      registerBeforeRounding registerProduct registerOutputs).certifyComposite
    (structuralChildren dataWidth dataFractionalBits twiddleWidth
      twiddleFractionalBits registerInputs multiplierLatency
      registerBeforeRounding registerProduct registerOutputs)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits
        registerInputs multiplierLatency registerBeforeRounding registerProduct
        registerOutputs)
      (structuralChildren dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)
      (childStructuralCertifications dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs))
    (fun _ => rfl)

end HTFFT.Silean.PipelinedFixedButterfly
