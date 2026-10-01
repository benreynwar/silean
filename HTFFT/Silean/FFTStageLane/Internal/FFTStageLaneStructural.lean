import HTFFT.Silean.FFTStageLane.Internal.FFTStageLaneStructure
import Silean.Authoring.ModuleRuleSchedules

/-! Contract-independent structural certification of one rolled-stage lane. -/

namespace HTFFT.Silean.FFTStageLane

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules
open HTFFT.FixedPoint

variable (dataFormat twiddleFormat : Format)
  (pairExponent phaseWidth laneAddressWidth lane : Nat)
  (twiddleDefinitionName : String)
  (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
    (twiddleSignalType twiddleFormat).Denote)
  (pipeline : PipelinedFixedButterfly.Pipeline)

@[reducible] private def childRules :
    ModuleStructuralCertification.Layer.ChildRules
      (body dataFormat twiddleFormat pairExponent phaseWidth laneAddressWidth
        lane twiddleDefinitionName twiddleValues pipeline) :=
  fun child => match child with
    | .firstDelay => ShiftRegister.rules (dataSignalType dataFormat)
        (2 ^ pairExponent) (Nat.two_pow_pos pairExponent)
    | .secondDelay => ShiftRegister.rules (dataSignalType dataFormat)
        (2 ^ pairExponent) (Nat.two_pow_pos pairExponent)
    | other => ModuleStructuralRules.whole
        ((instancePorts dataFormat twiddleFormat pairExponent phaseWidth
          laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
          |>.ports other)

private noncomputable def certifiedChildren :
    ModuleStructuralCertification.Layer.ChildStructures
      (body dataFormat twiddleFormat pairExponent phaseWidth laneAddressWidth
        lane twiddleDefinitionName twiddleValues pipeline)
      (childRules dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline) :=
  fun child => match child with
    | .laneAddress =>
        (Constant.certification (.vector laneAddressWidth .bit)
          (Internal.laneAddress laneAddressWidth lane)).structural
          |>.wholeCertifiedStructure
    | .addressConcat =>
        (VectorConcat.certification .bit laneAddressWidth phaseWidth).structural
          |>.wholeCertifiedStructure
    | .twiddle =>
        (ROM.certification twiddleDefinitionName
          (twiddleSignalType twiddleFormat)
          (laneAddressWidth + phaseWidth) twiddleValues).structural
          |>.wholeCertifiedStructure
    | .firstInputMux =>
        (Mux.certification (dataSignalType dataFormat)).structural
          |>.wholeCertifiedStructure
    | .secondInputMux =>
        (Mux.certification (dataSignalType dataFormat)).structural
          |>.wholeCertifiedStructure
    | .firstDelay => ShiftRegister.certified (dataSignalType dataFormat)
        (2 ^ pairExponent) (Nat.two_pow_pos pairExponent)
    | .secondDelay => ShiftRegister.certified (dataSignalType dataFormat)
        (2 ^ pairExponent) (Nat.two_pow_pos pairExponent)
    | .operandAMux =>
        (Mux.certification (dataSignalType dataFormat)).structural
          |>.wholeCertifiedStructure
    | .operandBMux =>
        (Mux.certification (dataSignalType dataFormat)).structural
          |>.wholeCertifiedStructure
    | .butterfly =>
        (PipelinedFixedButterfly.structuralCertification dataFormat
          twiddleFormat pipeline).wholeCertifiedStructure

private theorem certifiedChildren_moduleStructure (child) :
    (certifiedChildren dataFormat twiddleFormat pairExponent phaseWidth
      laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline child
        |>.moduleStructure) =
      structuralChildren dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline
        child := by
  cases child <;> rfl

module_complete_schedule completeSchedule
    (dataFormat : Format) (twiddleFormat : Format)
    (pairExponent : Nat) (phaseWidth : Nat)
    (laneAddressWidth : Nat) (lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    for body dataFormat twiddleFormat pairExponent phaseWidth laneAddressWidth
      lane twiddleDefinitionName twiddleValues pipeline
    with childRules dataFormat twiddleFormat pairExponent phaseWidth
      laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline :=
  [.laneAddress => .apply,
   .addressConcat => .apply,
   .twiddle => .apply,
   {.firstDelay, .secondDelay} => .output,
   .firstInputMux => .apply,
   .secondInputMux => .apply,
   .operandAMux => .apply,
   .operandBMux => .apply,
   .butterfly => .apply]

/-- One physical lane has a unique structural solution despite its deliberate
next-state feedback through the second delay line. -/
theorem Internal.structuralCertification :
    ModuleStructuralCertification
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline) :=
  (completeSchedule dataFormat twiddleFormat pairExponent phaseWidth
    laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
      |>.certifyComposite
        (structuralChildren dataFormat twiddleFormat pairExponent phaseWidth
          laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        (certifiedChildren dataFormat twiddleFormat pairExponent phaseWidth
          laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        (certifiedChildren_moduleStructure dataFormat twiddleFormat pairExponent
          phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
          pipeline)

end HTFFT.Silean.FFTStageLane
