import HTFFT.Silean.InitialReorder.Internal.InitialReorderSchedule

/-! Contract-independent structural certification of the concrete initial
reorder hierarchy. -/

namespace HTFFT.Silean.InitialReorder
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private theorem childStructuralCertifications (depth : Nat)
    (configuration : Configuration depth) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration child)
  | .trueSource => (Constant.certification .bit true).structural
  | .control => InitialReorder.Control.structuralCertification
      (addressWidth configuration)
  | .laneRotation =>
      (VectorReindex.certification .bit (addressWidth configuration)
        configuration.laneDepth
        (Internal.laneRotationLayout configuration)).structural
  | .preRotation =>
      (ConditionalNegate.certification configuration.laneDepth).structural
  | .preSplit =>
      (Internal.inputSplitter configuration).structuralCertification
  | .addressPayload lane =>
      InitialReorder.Lane.structuralCertification depth configuration lane
  | .payloadCombine =>
      (Internal.payloadCombiner configuration).structuralCertification
  | .preBarrel => BarrelShifter.structuralCertification
      (Internal.payloadType configuration) configuration.laneDepth
      configuration.initialBarrelPipeline
  | .payloadSplit =>
      (Internal.payloadSplitter configuration).structuralCertification
  | .readCycleAlign =>
      (ShiftRegister.certification
        (.vector (addressWidth configuration) .bit)
        configuration.frameLength configuration.frameLength_pos).structural
  | .readOrientationAlign =>
      (ShiftRegister.certification .bit configuration.frameLength
        configuration.frameLength_pos).structural
  | .readOrientationInvert => Primitives.notCertified.certification.structural
  | .readRotationAlign =>
      (ShiftRegister.certification (.vector configuration.laneDepth .bit)
        configuration.frameLength configuration.frameLength_pos).structural
  | .readPreRotation =>
      (ConditionalNegate.certification configuration.laneDepth).structural
  | .readAddressPayload lane =>
      InitialReorder.Lane.structuralCertification depth configuration lane
  | .readAddressCombine =>
      (Internal.addressCombiner configuration).structuralCertification
  | .readPreBarrel => BarrelShifter.structuralCertification
      (.vector (addressWidth configuration) .bit)
      configuration.laneDepth configuration.initialBarrelPipeline
  | .readAddressSplit =>
      (Internal.addressSplitter configuration).structuralCertification
  | .bank _ =>
      InitialReorder.BankLane.structuralCertification depth configuration
  | .bankCombine =>
      (Internal.bankCombiner configuration).structuralCertification
  | .postRotationAlign => OptionalShiftRegister.structuralCertification
      (.vector configuration.laneDepth .bit)
      (Internal.barrelLatency configuration + 1)
  | .postBarrel => BarrelShifter.structuralCertification
      (Internal.sampleType configuration) configuration.laneDepth
      configuration.initialBarrelPipeline
  | .markerAlign => ShiftRegister.structuralCertification .bit
      configuration.initialReorderLatency
      (Internal.markerLatency_pos configuration)

theorem Internal.structuralCertification (depth : Nat)
    (configuration : Configuration depth) :
    ModuleStructuralCertification (moduleStructure depth configuration) :=
  (Internal.completeSchedule depth configuration).certifyComposite
    (structuralChildren depth configuration)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration) (structuralChildren depth configuration)
      (childStructuralCertifications depth configuration))
    (fun _ => rfl)

end HTFFT.Silean.InitialReorder
