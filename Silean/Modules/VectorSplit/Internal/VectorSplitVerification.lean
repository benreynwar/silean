import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSplit.VectorSplit

namespace Silean.Modules.VectorSplit

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth where
  split := (splitter element leftWidth rightWidth).certified.certification,
  left := (leftCombiner element leftWidth).certified.certification,
  right := (rightCombiner element rightWidth).certified.certification

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth
    with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  output | .apply => [
    .split => Composition.SignalComponentRule.apply,
    .left => Composition.SignalComponentRule.apply,
    .right => Composition.SignalComponentRule.apply]
  state := []

private def splitInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (splitter element leftWidth rightWidth).ports.inputs.Values
  | .value => inputs .value

section LayerCertification

variable (element : SignalType) (leftWidth rightWidth : Nat)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element leftWidth rightWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element leftWidth rightWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element leftWidth rightWidth layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure element leftWidth rightWidth layerChildren)
    (cycleContract element leftWidth rightWidth)
    (stateCorresponds element leftWidth rightWidth layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have childMatch (child : Instance) := by
    letI : Subsingleton
        ((childContracts element leftWidth rightWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact childSolutionMatchesContract_of_subsingletonState
      (body := body element leftWidth rightWidth) layerChildren hierStep
      satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have splitOutputs : (hierStep.children .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (splitInputs element leftWidth rightWidth hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element leftWidth rightWidth) _ _ _).mp
      ((childMatch .split).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (body element leftWidth rightWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .split =
          splitInputs element leftWidth rightWidth hierStep.inputs := by
      funext input; cases input; rfl
    change (hierStep.children .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .split) at holds
    rw [inputsEqual] at holds
    exact holds
  have leftOutputs : (hierStep.children .left).outputs =
      (leftCombiner element leftWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .left) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .left).ruleHolds Composition.SignalComponentRule.apply)
  have rightOutputs : (hierStep.children .right).outputs =
      (rightCombiner element rightWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .right) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .right).ruleHolds Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change hierStep.outputs .left = leftPart (hierStep.inputs .value)
      rw [show hierStep.outputs .left =
          (hierStep.children .left).outputs .value by
        exact boundary .left]
      rw [congrFun leftOutputs .value]
      funext index
      change (hierStep.children .split).outputs (Fin.castAdd rightWidth index) =
        hierStep.inputs .value (Fin.castAdd rightWidth index)
      rw [splitOutputs]
      rfl
    · change hierStep.outputs .right = rightPart (hierStep.inputs .value)
      rw [show hierStep.outputs .right =
          (hierStep.children .right).outputs .value by
        exact boundary .right]
      rw [congrFun rightOutputs .value]
      funext index
      change (hierStep.children .split).outputs (Fin.natAdd leftWidth index) =
        hierStep.inputs .value (Fin.natAdd leftWidth index)
      rw [splitOutputs]
      rfl
  · rfl

end LayerCertification

module_cycle_certification certification (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat)
    for moduleStructure element leftWidth rightWidth
    via body element leftWidth rightWidth
    with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  schedules := derivedRuleSchedules element leftWidth rightWidth,
  structuralChildren := structuralChildren element leftWidth rightWidth,
  certifiedChildren := certifiedChildren element leftWidth rightWidth,
  structuresMatch := certifiedChildren_moduleStructure element leftWidth rightWidth,
  stateCorresponds := stateCorresponds element leftWidth rightWidth,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements element leftWidth rightWidth

end Silean.Modules.VectorSplit
