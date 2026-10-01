import HTFFT.Silean.InitialReorder.Lane.Internal.LaneStructure
import Silean.Authoring.ModuleRuleSchedules

namespace HTFFT.Silean.InitialReorder.Lane
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration lane)

private abbrev occurrence (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount) (child : Instance) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration lane) (wholeRules depth configuration lane) :=
  ⟨child, .apply⟩

module_complete_schedule completeSchedule (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    for body depth configuration lane
    with wholeRules depth configuration lane := from (
  [occurrence depth configuration lane .laneIndex,
   occurrence depth configuration lane .longAddress,
   occurrence depth configuration lane .reversedLongAddress,
   occurrence depth configuration lane .usedLongAddress,
   occurrence depth configuration lane .memoryAddress,
   occurrence depth configuration lane .payloadPack])

private theorem childStructuralCertifications (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount) :
    ∀ child, ModuleStructuralCertification
      (structuralChildren depth configuration lane child)
  | .laneIndex =>
      (Constant.certification (.vector configuration.laneDepth .bit)
        (BitVector.ofNat configuration.laneDepth lane.val)).structural
  | .longAddress =>
      (VectorConcat.certification .bit configuration.laneDepth
        (InitialReorder.addressWidth configuration)).structural
  | .reversedLongAddress =>
      (VectorReindex.certification .bit
        (configuration.laneDepth + InitialReorder.addressWidth configuration)
        (configuration.laneDepth + InitialReorder.addressWidth configuration)
        (Internal.reverseLayout configuration)).structural
  | .usedLongAddress =>
      (Mux.certification (.vector
        (configuration.laneDepth + InitialReorder.addressWidth configuration)
        .bit)).structural
  | .memoryAddress =>
      (VectorSlice.certification .bit configuration.laneDepth
        (InitialReorder.addressWidth configuration) 0).structural
  | .payloadPack =>
      (NamedTupleCombiner.certification
        (payloadMap configuration)).structural

theorem structuralCertification (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount) :
    ModuleStructuralCertification (moduleStructure depth configuration lane) :=
  (completeSchedule depth configuration lane).certifyComposite
    (structuralChildren depth configuration lane)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration lane)
      (structuralChildren depth configuration lane)
      (childStructuralCertifications depth configuration lane))
    (fun _ => rfl)

/-- The structural lane-address circuit produces its natural tagged payload.
Only the public equations of its children are used. -/
theorem result_of_solution (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    {step : HierStep (moduleStructure depth configuration lane)}
    (satisfies : (moduleStructure depth configuration lane).IsSolution step) :
    step.outputs .o_payload =
      resultValue configuration lane (step.inputs .i_data)
        (step.inputs .i_cycleAddress) (step.inputs .i_reversed) := by
  have laneRealizes := ModuleStructure.child_realizes satisfies .laneIndex
  have longRealizes := ModuleStructure.child_realizes satisfies .longAddress
  have reverseRealizes :=
    ModuleStructure.child_realizes satisfies .reversedLongAddress
  have muxRealizes := ModuleStructure.child_realizes satisfies .usedLongAddress
  have sliceRealizes := ModuleStructure.child_realizes satisfies .memoryAddress
  have packRealizes := ModuleStructure.child_realizes satisfies .payloadPack
  simp only [structuralChildren] at laneRealizes longRealizes reverseRealizes
  simp only [structuralChildren] at muxRealizes sliceRealizes packRealizes
  obtain ⟨_, _, laneAllowed⟩ := Constant.allowed_of_realization
    (.vector configuration.laneDepth .bit)
    (BitVector.ofNat configuration.laneDepth lane.val) laneRealizes
  have laneValue := Constant.output_of_allowed
    (.vector configuration.laneDepth .bit)
    (BitVector.ofNat configuration.laneDepth lane.val) laneAllowed
  have longValue := VectorConcat.result_of_realization .bit
    configuration.laneDepth (InitialReorder.addressWidth configuration)
    longRealizes
  have reverseValue := VectorReindex.output_of_realization .bit
    (configuration.laneDepth + InitialReorder.addressWidth configuration)
    (configuration.laneDepth + InitialReorder.addressWidth configuration)
    (Internal.reverseLayout configuration) reverseRealizes
  have usedValue := Mux.result_of_realization
    (.vector
      (configuration.laneDepth + InitialReorder.addressWidth configuration) .bit)
    muxRealizes
  have addressValue := VectorSlice.result_of_realization .bit
    configuration.laneDepth (InitialReorder.addressWidth configuration) 0
    sliceRealizes
  have payloadValue := NamedTupleCombiner.value_of_realization
    (payloadMap configuration) packRealizes
  have laneInput := ModuleStructure.child_input satisfies .longAddress .left
  have cycleInput := ModuleStructure.child_input satisfies .longAddress .right
  have reverseInput :=
    ModuleStructure.child_input satisfies .reversedLongAddress .input
  have muxSelect := ModuleStructure.child_input satisfies .usedLongAddress .select
  have muxFalse :=
    ModuleStructure.child_input satisfies .usedLongAddress .whenFalse
  have muxTrue := ModuleStructure.child_input satisfies .usedLongAddress .whenTrue
  have sliceInput := ModuleStructure.child_input satisfies .memoryAddress .value
  have packData := ModuleStructure.child_input satisfies .payloadPack .data
  have packAddress :=
    ModuleStructure.child_input satisfies .payloadPack .address
  have boundary := ModuleStructure.parent_output satisfies .o_payload
  change (step.children .laneIndex).outputs .output =
    BitVector.ofNat configuration.laneDepth lane.val at laneValue
  change (step.children .longAddress).outputs .result =
    VectorConcat.concat ((step.children .longAddress).inputs .left)
      ((step.children .longAddress).inputs .right) at longValue
  change (step.children .reversedLongAddress).outputs .output =
    VectorReindex.apply (Internal.reverseLayout configuration)
      ((step.children .reversedLongAddress).inputs .input) at reverseValue
  change (step.children .usedLongAddress).outputs .result =
    bif (step.children .usedLongAddress).inputs .select then
      (step.children .usedLongAddress).inputs .whenTrue
    else (step.children .usedLongAddress).inputs .whenFalse at usedValue
  change (step.children .memoryAddress).outputs .result =
    VectorSlice.slice ((step.children .memoryAddress).inputs .value)
      at addressValue
  change (step.children .payloadPack).outputs .value =
    NamedTupleCombiner.combinedValue (payloadMap configuration)
      (step.children .payloadPack).inputs at payloadValue
  change (step.children .longAddress).inputs .left =
    (step.children .laneIndex).outputs .output at laneInput
  change (step.children .longAddress).inputs .right =
    step.inputs .i_cycleAddress at cycleInput
  change (step.children .reversedLongAddress).inputs .input =
    (step.children .longAddress).outputs .result at reverseInput
  change (step.children .usedLongAddress).inputs .select =
    step.inputs .i_reversed at muxSelect
  change (step.children .usedLongAddress).inputs .whenFalse =
    (step.children .longAddress).outputs .result at muxFalse
  change (step.children .usedLongAddress).inputs .whenTrue =
    (step.children .reversedLongAddress).outputs .output at muxTrue
  change (step.children .memoryAddress).inputs .value =
    (step.children .usedLongAddress).outputs .result at sliceInput
  change (step.children .payloadPack).inputs .data =
    step.inputs .i_data at packData
  change (step.children .payloadPack).inputs .address =
    (step.children .memoryAddress).outputs .result at packAddress
  change step.outputs .o_payload =
    (step.children .payloadPack).outputs .value at boundary
  rw [boundary, payloadValue]
  unfold resultValue
  apply congrArg (payloadMap configuration).pack
  funext field
  cases field with
  | data => exact packData
  | address =>
      rw [packAddress, addressValue, sliceInput, usedValue, muxSelect,
        muxFalse, muxTrue, reverseValue, reverseInput, longValue,
        laneInput, laneValue, cycleInput]
      rfl

/-- The same structural circuit exposes the address independently of the
tagged write payload, allowing a read-address path to share its natural
address calculation without carrying unused sample bits. -/
theorem address_of_solution (depth : Nat)
    (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    {step : HierStep (moduleStructure depth configuration lane)}
    (satisfies : (moduleStructure depth configuration lane).IsSolution step) :
    step.outputs .o_address =
      memoryAddress configuration lane (step.inputs .i_cycleAddress)
        (step.inputs .i_reversed) := by
  have result := result_of_solution depth configuration lane satisfies
  have payloadAddress := congrArg
    (fun payload => NamedTupleSplitter.splitValue
      (payloadMap configuration) payload .address) result
  have boundary := ModuleStructure.parent_output satisfies .o_address
  have payloadBoundary := ModuleStructure.parent_output satisfies .o_payload
  have addressWire := ModuleStructure.child_input satisfies .payloadPack .address
  have packRealizes := ModuleStructure.child_realizes satisfies .payloadPack
  simp only [structuralChildren] at packRealizes
  have payloadValue := NamedTupleCombiner.value_of_realization
    (payloadMap configuration) packRealizes
  change step.outputs .o_address =
    (step.children .memoryAddress).outputs .result at boundary
  change step.outputs .o_payload =
    (step.children .payloadPack).outputs .value at payloadBoundary
  change (step.children .payloadPack).inputs .address =
    (step.children .memoryAddress).outputs .result at addressWire
  change (step.children .payloadPack).outputs .value =
    NamedTupleCombiner.combinedValue (payloadMap configuration)
      (step.children .payloadPack).inputs at payloadValue
  have packedAddress := congrArg
    (fun payload => NamedTupleSplitter.splitValue
      (payloadMap configuration) payload .address) payloadValue
  simp only [NamedTupleCombiner.combinedValue_eq_pack,
    NamedTupleSplitter.splitValue_pack] at packedAddress
  calc
    step.outputs .o_address =
        (step.children .memoryAddress).outputs .result := boundary
    _ = (step.children .payloadPack).inputs .address := addressWire.symm
    _ = NamedTupleSplitter.splitValue (payloadMap configuration)
        ((step.children .payloadPack).outputs .value) .address :=
      packedAddress.symm
    _ = NamedTupleSplitter.splitValue (payloadMap configuration)
        (step.outputs .o_payload) .address := by rw [payloadBoundary]
    _ = NamedTupleSplitter.splitValue (payloadMap configuration)
        (resultValue configuration lane (step.inputs .i_data)
          (step.inputs .i_cycleAddress) (step.inputs .i_reversed)) .address :=
      payloadAddress
    _ = memoryAddress configuration lane (step.inputs .i_cycleAddress)
        (step.inputs .i_reversed) := resultValue_address _ _ _ _ _

end HTFFT.Silean.InitialReorder.Lane
