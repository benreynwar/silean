import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.CarrySaveTree.Internal.CarrySaveTreeStructure

/-! Direct structural proof of the relational carry-save-tree contract. -/

namespace Silean.Modules.CarrySaveTree

open Silean
open Silean.Authoring

private abbrev wholeRules (body : ModuleBody) :=
  ModuleStructuralCertification.Layer.wholeChildRules body

module_complete_schedule zeroCompleteSchedule (width : Nat)
    for Internal.zeroBody width with wholeRules (Internal.zeroBody width) := [
      .split => ModuleStructuralRules.WholeRule.apply,
      .zeroA => ModuleStructuralRules.WholeRule.apply,
      .zeroB => ModuleStructuralRules.WholeRule.apply]

module_complete_schedule oneCompleteSchedule (width : Nat)
    for Internal.oneBody width with wholeRules (Internal.oneBody width) := [
      .split => ModuleStructuralRules.WholeRule.apply,
      .zero => ModuleStructuralRules.WholeRule.apply]

module_complete_schedule twoCompleteSchedule (width : Nat)
    for Internal.twoBody width with wholeRules (Internal.twoBody width) := [
      .split => ModuleStructuralRules.WholeRule.apply]

module_complete_schedule recursiveCompleteSchedule (width : Nat)
    (operandCount : Nat) for Internal.recursiveBody width operandCount
    with wholeRules (Internal.recursiveBody width operandCount) := [
      .layer => ModuleStructuralRules.WholeRule.apply,
      .rest => ModuleStructuralRules.WholeRule.apply]

/-- Contract-independent structural certification of the recursive tree. -/
theorem Internal.structuralCertification (width : Nat) :
    ∀ operandCount : Nat,
      ModuleStructuralCertification (moduleStructure width operandCount)
  | 0 => by
      let structures : (child : (Internal.zeroBody width).instancePorts.Name) →
          ModuleStructure ((Internal.zeroBody width).instancePorts.ports child) :=
        fun
          | .split => .splitter (Internal.inputSplitter width 0)
          | .zeroA | .zeroB =>
              Modules.Constant.moduleStructure (.vector width .bit)
                (Internal.zeroValue width)
      let certifications : ∀ child,
          ModuleStructuralCertification (structures child) := fun
        | .split => (Internal.inputSplitter width 0).structuralCertification
        | .zeroA | .zeroB =>
            (Modules.Constant.certification (.vector width .bit)
              (Internal.zeroValue width)).structural
      change ModuleStructuralCertification
        (.composite (Internal.zeroBody width) structures)
      exact (zeroCompleteSchedule width).certifyComposite structures
        (ModuleStructuralCertification.Layer.wholeCertifiedChildren
          (Internal.zeroBody width) structures certifications)
        (fun _ => rfl)
  | 1 => by
      let structures : (child : (Internal.oneBody width).instancePorts.Name) →
          ModuleStructure ((Internal.oneBody width).instancePorts.ports child) :=
        fun
          | .split => .splitter (Internal.inputSplitter width 1)
          | .zero => Modules.Constant.moduleStructure (.vector width .bit)
              (Internal.zeroValue width)
      let certifications : ∀ child,
          ModuleStructuralCertification (structures child) := fun
        | .split => (Internal.inputSplitter width 1).structuralCertification
        | .zero => (Modules.Constant.certification (.vector width .bit)
            (Internal.zeroValue width)).structural
      change ModuleStructuralCertification
        (.composite (Internal.oneBody width) structures)
      exact (oneCompleteSchedule width).certifyComposite structures
        (ModuleStructuralCertification.Layer.wholeCertifiedChildren
          (Internal.oneBody width) structures certifications)
        (fun _ => rfl)
  | 2 => by
      let structures : (child : (Internal.twoBody width).instancePorts.Name) →
          ModuleStructure ((Internal.twoBody width).instancePorts.ports child) :=
        fun | .split => .splitter (Internal.inputSplitter width 2)
      let certifications : ∀ child,
          ModuleStructuralCertification (structures child) := fun
        | .split => (Internal.inputSplitter width 2).structuralCertification
      change ModuleStructuralCertification
        (.composite (Internal.twoBody width) structures)
      exact (twoCompleteSchedule width).certifyComposite structures
        (ModuleStructuralCertification.Layer.wholeCertifiedChildren
          (Internal.twoBody width) structures certifications)
        (fun _ => rfl)
  | operandCount + 3 => by
      let structures :
          (child : (Internal.recursiveBody width
            (operandCount + 3)).instancePorts.Name) →
            ModuleStructure
              ((Internal.recursiveBody width
                (operandCount + 3)).instancePorts.ports child) :=
        fun
          | .layer => CarrySaveLayer.moduleStructure width (operandCount + 3)
          | .rest => Internal.moduleStructure width
              (CarrySaveLayer.reducedCount (operandCount + 3))
      let certifications : ∀ child,
          ModuleStructuralCertification (structures child) := fun
        | .layer => CarrySaveLayer.structuralCertification width
            (operandCount + 3)
        | .rest => Internal.structuralCertification width
            (CarrySaveLayer.reducedCount (operandCount + 3))
      have scheduled : ModuleStructuralCertification
          (.composite (Internal.recursiveBody width (operandCount + 3))
            structures) :=
        (recursiveCompleteSchedule width
          (operandCount + 3)).certifyComposite structures
          (ModuleStructuralCertification.Layer.wholeCertifiedChildren
            (Internal.recursiveBody width (operandCount + 3))
            structures certifications)
          (fun _ => rfl)
      have structureEq :
          (.composite (Internal.recursiveBody width (operandCount + 3))
            structures) = moduleStructure width (operandCount + 3) := by
        symm
        change Internal.moduleStructure width (operandCount + 3) = _
        rw [Internal.moduleStructure.eq_def]
        congr
      exact ModuleStructuralCertification.transport structureEq scheduled
termination_by operandCount => operandCount
decreasing_by
  exact CarrySaveLayer.reducedCount_lt (operandCount + 3) (by omega)

theorem Internal.contract_of_realization (width : Nat) :
    ∀ (operandCount : Nat)
      {step : (moduleStructure width operandCount).Step},
      (moduleStructure width operandCount).Realizes step →
        contract width operandCount step.inputs step.outputs
  | 0, step, realizes => by
      rcases realizes with ⟨hierStep, satisfies, rfl⟩

      have zeroARealizes := ModuleStructure.child_realizes satisfies (.zeroA)
      have zeroBRealizes := ModuleStructure.child_realizes satisfies (.zeroB)
      change (Modules.Constant.moduleStructure (.vector width .bit)
        (zeroValue width)).Realizes _ at zeroARealizes zeroBRealizes
      obtain ⟨_, _, zeroAAllowed⟩ :=
        Modules.Constant.allowed_of_realization (.vector width .bit)
          (zeroValue width) zeroARealizes
      obtain ⟨_, _, zeroBAllowed⟩ :=
        Modules.Constant.allowed_of_realization (.vector width .bit)
          (zeroValue width) zeroBRealizes
      have zeroAOutput := Modules.Constant.output_of_allowed
        (.vector width .bit) (zeroValue width) zeroAAllowed
      have zeroBOutput := Modules.Constant.output_of_allowed
        (.vector width .bit) (zeroValue width) zeroBAllowed
      simp only [HierStep.step_outputs] at zeroAOutput zeroBOutput

      have outputA : hierStep.outputs .resultA = zeroValue width := by
        calc
          hierStep.outputs .resultA =
              (hierStep.children .zeroA).outputs .output := by
            have equation := ModuleStructure.parent_output satisfies (.resultA)
            change hierStep.outputs .resultA =
              (hierStep.children .zeroA).outputs .output at equation
            exact equation
          _ = zeroValue width := zeroAOutput
      have outputB : hierStep.outputs .resultB = zeroValue width := by
        calc
          hierStep.outputs .resultB =
              (hierStep.children .zeroB).outputs .output := by
            have equation := ModuleStructure.parent_output satisfies (.resultB)
            change hierStep.outputs .resultB =
              (hierStep.children .zeroB).outputs .output at equation
            exact equation
          _ = zeroValue width := zeroBOutput

      change Accepts width 0 (hierStep.inputs .operands)
        (hierStep.outputs .resultA) (hierStep.outputs .resultB)
      rw [accepts_zero_iff]
      exact ⟨outputA, outputB⟩

  | 1, step, realizes => by
      rcases realizes with ⟨hierStep, satisfies, rfl⟩

      have splitInput : (hierStep.children .split).inputs .value =
          hierStep.inputs .operands := by
        have equation := ModuleStructure.child_input satisfies (.split) (.value)
        change (hierStep.children .split).inputs .value =
          hierStep.inputs .operands at equation
        exact equation
      have splitOutputs : (hierStep.children .split).outputs =
          (inputSplitter width 1).outputValues
            (hierStep.children .split).inputs := by
        exact ModuleStructure.splitter_outputs_of_solution
          (ModuleStructure.child_isSolution satisfies (.split))
      have splitAtZero : (hierStep.children .split).outputs 0 =
          hierStep.inputs .operands 0 := by
        calc
          (hierStep.children .split).outputs 0 =
              (inputSplitter width 1).outputValues
                (hierStep.children .split).inputs 0 :=
            congrFun splitOutputs 0
          _ = (hierStep.children .split).inputs .value 0 := rfl
          _ = hierStep.inputs .operands 0 := congrFun splitInput 0

      have zeroRealizes := ModuleStructure.child_realizes satisfies (.zero)
      change (Modules.Constant.moduleStructure (.vector width .bit)
        (zeroValue width)).Realizes _ at zeroRealizes
      obtain ⟨_, _, zeroAllowed⟩ :=
        Modules.Constant.allowed_of_realization (.vector width .bit)
          (zeroValue width) zeroRealizes
      have zeroOutput := Modules.Constant.output_of_allowed
        (.vector width .bit) (zeroValue width) zeroAllowed
      simp only [HierStep.step_outputs] at zeroOutput

      have outputA : hierStep.outputs .resultA =
          hierStep.inputs .operands 0 := by
        calc
          hierStep.outputs .resultA =
              (hierStep.children .split).outputs 0 := by
            have equation := ModuleStructure.parent_output satisfies (.resultA)
            change hierStep.outputs .resultA =
              (hierStep.children .split).outputs 0 at equation
            exact equation
          _ = hierStep.inputs .operands 0 := splitAtZero
      have outputB : hierStep.outputs .resultB = zeroValue width := by
        calc
          hierStep.outputs .resultB =
              (hierStep.children .zero).outputs .output := by
            have equation := ModuleStructure.parent_output satisfies (.resultB)
            change hierStep.outputs .resultB =
              (hierStep.children .zero).outputs .output at equation
            exact equation
          _ = zeroValue width := zeroOutput

      change Accepts width 1 (hierStep.inputs .operands)
        (hierStep.outputs .resultA) (hierStep.outputs .resultB)
      rw [accepts_one_iff]
      exact ⟨outputA, outputB⟩

  | 2, step, realizes => by
      rcases realizes with ⟨hierStep, satisfies, rfl⟩

      have splitInput : (hierStep.children .split).inputs .value =
          hierStep.inputs .operands := by
        have equation := ModuleStructure.child_input satisfies (.split) (.value)
        change (hierStep.children .split).inputs .value =
          hierStep.inputs .operands at equation
        exact equation
      have splitOutputs : (hierStep.children .split).outputs =
          (inputSplitter width 2).outputValues
            (hierStep.children .split).inputs := by
        exact ModuleStructure.splitter_outputs_of_solution
          (ModuleStructure.child_isSolution satisfies (.split))
      have splitAt (index : Fin 2) :
          (hierStep.children .split).outputs index =
            hierStep.inputs .operands index := by
        calc
          (hierStep.children .split).outputs index =
              (inputSplitter width 2).outputValues
                (hierStep.children .split).inputs index :=
            congrFun splitOutputs index
          _ = (hierStep.children .split).inputs .value index := rfl
          _ = hierStep.inputs .operands index := congrFun splitInput index

      have outputA : hierStep.outputs .resultA =
          hierStep.inputs .operands 0 := by
        calc
          hierStep.outputs .resultA =
              (hierStep.children .split).outputs 0 := by
            have equation := ModuleStructure.parent_output satisfies (.resultA)
            change hierStep.outputs .resultA =
              (hierStep.children .split).outputs 0 at equation
            exact equation
          _ = hierStep.inputs .operands 0 := splitAt 0
      have outputB : hierStep.outputs .resultB =
          hierStep.inputs .operands 1 := by
        calc
          hierStep.outputs .resultB =
              (hierStep.children .split).outputs 1 := by
            have equation := ModuleStructure.parent_output satisfies (.resultB)
            change hierStep.outputs .resultB =
              (hierStep.children .split).outputs 1 at equation
            exact equation
          _ = hierStep.inputs .operands 1 := splitAt 1

      change Accepts width 2 (hierStep.inputs .operands)
        (hierStep.outputs .resultA) (hierStep.outputs .resultB)
      rw [accepts_two_iff]
      exact ⟨outputA, outputB⟩

  | operandCount + 3, step, realizes => by
      have structureEq : moduleStructure width (operandCount + 3) =
          ModuleStructure.composite
            (recursiveBody width (operandCount + 3)) (fun
              | .layer => CarrySaveLayer.moduleStructure width (operandCount + 3)
              | .rest => Internal.moduleStructure width
                  (CarrySaveLayer.reducedCount (operandCount + 3))) := by
        change Internal.moduleStructure width (operandCount + 3) = _
        rw [Internal.moduleStructure.eq_def]
        congr
      refine ModuleStructure.boundary_property_of_structure_eq structureEq
        (property := contract width (operandCount + 3)) ?_ realizes
      intro unfoldedStep unfoldedRealizes
      rcases unfoldedRealizes with ⟨hierStep, satisfies, rfl⟩
      change contract width (operandCount + 3) hierStep.step.inputs
        hierStep.step.outputs

      have layerRealizes := ModuleStructure.child_realizes satisfies (.layer)
      have restRealizes := ModuleStructure.child_realizes satisfies (.rest)
      change (CarrySaveLayer.moduleStructure width (operandCount + 3)).Realizes _
        at layerRealizes
      change (moduleStructure width
        (CarrySaveLayer.reducedCount (operandCount + 3))).Realizes _
          at restRealizes
      have layerAccepted := CarrySaveLayer.contract_of_realization
        width (operandCount + 3) layerRealizes
      have restAccepted := Internal.contract_of_realization width
        (CarrySaveLayer.reducedCount (operandCount + 3)) restRealizes

      have layerInput : (hierStep.children .layer).inputs .operands =
          hierStep.inputs .operands := by
        simpa only [recursiveWiring, EndpointContext.moduleInput,
          SignalSource.value] using
          ModuleStructure.child_input satisfies (.layer) (.operands)
      have restInput : (hierStep.children .rest).inputs .operands =
          (hierStep.children .layer).outputs .reduced := by
        simpa only [recursiveWiring, EndpointContext.instanceOutput,
          SignalSource.value] using
          ModuleStructure.child_input satisfies (.rest) (.operands)
      have outputA : hierStep.outputs .resultA =
          (hierStep.children .rest).outputs .resultA := by
        simpa only [recursiveWiring, EndpointContext.instanceOutput,
          SignalSource.value] using
          ModuleStructure.parent_output satisfies (.resultA)
      have outputB : hierStep.outputs .resultB =
          (hierStep.children .rest).outputs .resultB := by
        simpa only [recursiveWiring, EndpointContext.instanceOutput,
          SignalSource.value] using
          ModuleStructure.parent_output satisfies (.resultB)

      have layerPreserves := CarrySaveLayer.preservesTotal_of_contract
        width (operandCount + 3) layerAccepted
      have restPreserves := preservesTotal_of_contract width
        (CarrySaveLayer.reducedCount (operandCount + 3)) restAccepted

      change Accepts width (operandCount + 3) (hierStep.inputs .operands)
        (hierStep.outputs .resultA) (hierStep.outputs .resultB)
      constructor
      · unfold PreservesTotal
        calc
          outputTotal width (hierStep.outputs .resultA)
                (hierStep.outputs .resultB) % BitVector.cardinality width =
              outputTotal width ((hierStep.children .rest).outputs .resultA)
                ((hierStep.children .rest).outputs .resultB) %
                  BitVector.cardinality width := by rw [outputA, outputB]
          _ = inputTotal width (CarrySaveLayer.reducedCount (operandCount + 3))
                ((hierStep.children .rest).inputs .operands) %
                  BitVector.cardinality width := restPreserves
          _ = CarrySaveLayer.total width
                (CarrySaveLayer.reducedCount (operandCount + 3))
                ((hierStep.children .layer).outputs .reduced) %
                  BitVector.cardinality width := by rw [restInput]; rfl
          _ = CarrySaveLayer.total width (operandCount + 3)
                ((hierStep.children .layer).inputs .operands) %
                  BitVector.cardinality width := layerPreserves
          _ = inputTotal width (operandCount + 3)
                (hierStep.inputs .operands) % BitVector.cardinality width := by
              rw [layerInput]
              rfl
      · trivial
termination_by operandCount => operandCount
decreasing_by
  exact CarrySaveLayer.reducedCount_lt (operandCount + 3) (by omega)

end Silean.Modules.CarrySaveTree
