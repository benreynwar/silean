import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.CarrySaveAdder.Internal.CarrySaveAdderArithmetic
import Silean.Modules.CarrySaveAdder.Internal.CarrySaveAdderStructure

/-! Structural certification for `CarrySaveAdder`. -/

namespace Silean.Modules.CarrySaveAdder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat)
    for body width where
  iASplit := (Internal.splitter width).certified.certification,
  iBSplit := (Internal.splitter width).certified.certification,
  iCSplit := (Internal.splitter width).certified.certification,
  adder (_index : Fin width) := FullAdder.certification,
  sumCombine := (Internal.combiner width).certified.certification,
  rawCarryCombine := (Internal.combiner width).certified.certification,
  carryShift := VectorLayout.certification width width
    (Internal.carryShiftLayout width)

private abbrev iASplitOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.iASplit, Composition.SignalComponentRule.apply⟩

private abbrev iBSplitOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.iBSplit, Composition.SignalComponentRule.apply⟩

private abbrev iCSplitOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.iCSplit, Composition.SignalComponentRule.apply⟩

private abbrev adderSumOccurrence (width : Nat) (index : Fin width) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.adder index, FullAdder.Rule.sum⟩

private abbrev adderCarryOccurrence (width : Nat) (index : Fin width) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.adder index, FullAdder.Rule.carryOut⟩

private abbrev sumCombineOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.sumCombine, Composition.SignalComponentRule.apply⟩

private abbrev rawCarryCombineOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.rawCarryCombine, Composition.SignalComponentRule.apply⟩

private abbrev carryShiftOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.carryShift, VectorLayout.Rule.apply⟩

module_rule_schedules derivedRuleSchedules (width : Nat)
    for body width with childContracts width implementing cycleContract width where
  output
    | .apply => from ([iASplitOccurrence width, iBSplitOccurrence width,
        iCSplitOccurrence width] ++
      (Enumeration.fin width).values.map (adderSumOccurrence width) ++
      (Enumeration.fin width).values.map (adderCarryOccurrence width) ++
      [sumCombineOccurrence width, rawCarryCombineOccurrence width,
        carryShiftOccurrence width])
  state := []

private theorem apply_carryShiftLayout (width : Nat)
    (iA iB iC : Fin width → Bool) :
    VectorLayout.apply (Internal.carryShiftLayout width)
        (Internal.rawCarryValue width iA iB iC) =
      carryValue width iA iB iC := by
  funext index
  unfold VectorLayout.apply Internal.carryShiftLayout carryValue
    Internal.rawCarryValue
  by_cases nonzero : 0 < index.val
  · simp [nonzero]
  · have zero : index.val = 0 := by omega
    simp [zero]

section LayerCertification

variable (width : Nat)
  (layerChildren : ChildStructures (body width) (childContracts width))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body width from
    layerChildren, hierStep, satisfies
  have iAOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (Internal.splitter width) _ _ _).mp
      ((childMatch .iASplit).ruleHolds Composition.SignalComponentRule.apply)
  have iBOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (Internal.splitter width) _ _ _).mp
      ((childMatch .iBSplit).ruleHolds Composition.SignalComponentRule.apply)
  have iCOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (Internal.splitter width) _ _ _).mp
      ((childMatch .iCSplit).ruleHolds Composition.SignalComponentRule.apply)
  have iABit (index : Fin width) :
      (hierStep.children .iASplit).outputs index = hierStep.inputs .iA index := by
    exact congrFun iAOutputs index
  have iBBit (index : Fin width) :
      (hierStep.children .iBSplit).outputs index = hierStep.inputs .iB index := by
    exact congrFun iBOutputs index
  have iCBit (index : Fin width) :
      (hierStep.children .iCSplit).outputs index = hierStep.inputs .iC index := by
    exact congrFun iCOutputs index
  have adderSum (index : Fin width) :
      (hierStep.children (.adder index)).outputs .sum =
        sumBit (hierStep.inputs .iA index)
          (hierStep.inputs .iB index) (hierStep.inputs .iC index) := by
    have equation := (childMatch (.adder index)).boundaryOutput
      FullAdder.cycleContract.sumEquation
    change (hierStep.children (.adder index)).outputs .sum =
      FullAdder.sumValue ((hierStep.children .iASplit).outputs index)
        ((hierStep.children .iBSplit).outputs index)
        ((hierStep.children .iCSplit).outputs index) at equation
    simpa [iABit index, iBBit index, iCBit index,
      Internal.fullAdder_sumValue_eq_sumBit] using equation
  have adderCarry (index : Fin width) :
      (hierStep.children (.adder index)).outputs .carryOut =
        carryBit (hierStep.inputs .iA index)
          (hierStep.inputs .iB index) (hierStep.inputs .iC index) := by
    have equation := (childMatch (.adder index)).boundaryOutput
      FullAdder.cycleContract.carryOutEquation
    change (hierStep.children (.adder index)).outputs .carryOut =
      FullAdder.carryValue ((hierStep.children .iASplit).outputs index)
        ((hierStep.children .iBSplit).outputs index)
        ((hierStep.children .iCSplit).outputs index) at equation
    simpa [iABit index, iBBit index, iCBit index,
      Internal.fullAdder_carryValue_eq_carryBit] using equation
  have sumCombinedRaw : (hierStep.children .sumCombine).outputs .value =
      fun index => (hierStep.children (.adder index)).outputs .sum := by
    have equal := (Composition.SignalCombiner.outputRule_holds_iff
      (Internal.combiner width) _ _ _).mp
        ((childMatch .sumCombine).ruleHolds
          Composition.SignalComponentRule.apply)
    exact congrFun equal Composition.AggregatePort.value
  have rawCarryCombinedRaw :
      (hierStep.children .rawCarryCombine).outputs .value =
        fun index => (hierStep.children (.adder index)).outputs .carryOut := by
    have equal := (Composition.SignalCombiner.outputRule_holds_iff
      (Internal.combiner width) _ _ _).mp
        ((childMatch .rawCarryCombine).ruleHolds
          Composition.SignalComponentRule.apply)
    exact congrFun equal Composition.AggregatePort.value
  have sumCombined : (hierStep.children .sumCombine).outputs .value =
      sumValue width (hierStep.inputs .iA) (hierStep.inputs .iB)
        (hierStep.inputs .iC) := by
    rw [sumCombinedRaw]
    funext index
    exact adderSum index
  have rawCarryCombined :
      (hierStep.children .rawCarryCombine).outputs .value =
        Internal.rawCarryValue width (hierStep.inputs .iA) (hierStep.inputs .iB)
          (hierStep.inputs .iC) := by
    rw [rawCarryCombinedRaw]
    funext index
    exact adderCarry index
  have shifted := VectorLayout.cycleContract.output width width
    (Internal.carryShiftLayout width) (childMatch .carryShift).allowed
  change (hierStep.children .carryShift).outputs .output =
    VectorLayout.apply (Internal.carryShiftLayout width)
      ((hierStep.children .rawCarryCombine).outputs .value) at shifted
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .sum =
        sumValue width (hierStep.inputs .iA) (hierStep.inputs .iB)
          (hierStep.inputs .iC) ∧
      hierStep.outputs .carry =
        carryValue width (hierStep.inputs .iA) (hierStep.inputs .iB)
          (hierStep.inputs .iC)
    constructor
    · rw [show hierStep.outputs .sum =
          (hierStep.children .sumCombine).outputs .value by
        exact satisfies.1 .sum]
      exact sumCombined
    · rw [show hierStep.outputs .carry =
          (hierStep.children .carryShift).outputs .output by
        exact satisfies.1 .carry]
      rw [shifted, rawCarryCombined, apply_carryShiftLayout]
  · rfl

end LayerCertification

module_cycle_certification certification (width : Nat)
    for moduleStructure width via body width with childContracts width
    implementing cycleContract width where
  schedules := derivedRuleSchedules width,
  structuralChildren := structuralChildren width,
  certifiedChildren := certifiedChildren width,
  structuresMatch := certifiedChildren_moduleStructure width,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements width

end Silean.Modules.CarrySaveAdder
