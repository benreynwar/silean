import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorConcat.VectorConcat

namespace Silean.Modules.VectorConcat

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth where
  leftSplit := (leftSplitter element leftWidth).certified.certification,
  rightSplit := (rightSplitter element rightWidth).certified.certification,
  combine := (combiner element leftWidth rightWidth).certified.certification

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth
    with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  output | .apply => [
    .leftSplit => Composition.SignalComponentRule.apply,
    .rightSplit => Composition.SignalComponentRule.apply,
    .combine => Composition.SignalComponentRule.apply]
  state := []

private def leftInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (leftSplitter element leftWidth).ports.inputs.Values
  | .value => inputs .left

private def rightInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (rightSplitter element rightWidth).ports.inputs.Values
  | .value => inputs .right

private def combineInputs
    (left : (leftSplitter element leftWidth).ports.outputs.Values)
    (right : (rightSplitter element rightWidth).ports.outputs.Values) :
    (combiner element leftWidth rightWidth).ports.inputs.Values := fun index =>
  Fin.addCases (fun leftIndex => left leftIndex)
    (fun rightIndex => right rightIndex) index

section LayerCertification

variable (element : SignalType) (leftWidth rightWidth : Nat)
  (layerChildren : (child : (instancePorts element leftWidth rightWidth).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element leftWidth rightWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element leftWidth rightWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element leftWidth rightWidth layerChildren).State) :
    Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (certificationStructure element leftWidth rightWidth layerChildren)
      (cycleContract element leftWidth rightWidth)
      (stateCorresponds element leftWidth rightWidth layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have childMatch (child : (instancePorts element leftWidth rightWidth).Name) := by
    letI : Subsingleton
        ((childContracts element leftWidth rightWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      (body := body element leftWidth rightWidth) layerChildren hierStep
        satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have leftOutputs : (hierStep.children .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues
        (leftInputs hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (leftSplitter element leftWidth) _ _ _).mp
      ((childMatch .leftSplit).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (body element leftWidth rightWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .leftSplit =
          leftInputs hierStep.inputs := by funext input; cases input; rfl
    change (hierStep.children .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .leftSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have rightOutputs : (hierStep.children .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues
        (rightInputs hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (rightSplitter element rightWidth) _ _ _).mp
      ((childMatch .rightSplit).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (body element leftWidth rightWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .rightSplit =
          rightInputs hierStep.inputs := by funext input; cases input; rfl
    change (hierStep.children .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .rightSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have combineOutputs : (hierStep.children .combine).outputs =
      (combiner element leftWidth rightWidth).outputValues
        ((body element leftWidth rightWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .combine) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .combine).ruleHolds Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .result =
      concat (hierStep.inputs .left) (hierStep.inputs .right)
    rw [show hierStep.outputs .result =
        (hierStep.children .combine).outputs .value by
      exact boundary .result]
    rw [congrFun combineOutputs .value]
    rw [show (body element leftWidth rightWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .combine =
          combineInputs (hierStep.children .leftSplit).outputs
            (hierStep.children .rightSplit).outputs by
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro leftIndex
        simp [Wiring.childInputValues, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]
        change (hierStep.children .leftSplit).outputs leftIndex =
          (hierStep.children .leftSplit).outputs leftIndex
        rfl
      · intro rightIndex
        simp [Wiring.childInputValues, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]
        change (hierStep.children .rightSplit).outputs rightIndex =
          (hierStep.children .rightSplit).outputs rightIndex
        rfl
    ]
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro leftIndex
      simp [combiner, Composition.SignalCombiner.outputValues, combineInputs, concat]
      rw [leftOutputs]
      rfl
    · intro rightIndex
      simp [combiner, Composition.SignalCombiner.outputValues, combineInputs, concat]
      rw [rightOutputs]
      rfl
  · rfl

end LayerCertification

module_cycle_certification certification (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for moduleStructure element leftWidth rightWidth
    via body element leftWidth rightWidth with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  schedules := derivedRuleSchedules element leftWidth rightWidth,
  structuralChildren := structuralChildren element leftWidth rightWidth,
  certifiedChildren := certifiedChildren element leftWidth rightWidth,
  structuresMatch := certifiedChildren_moduleStructure element leftWidth rightWidth,
  stateCorresponds := stateCorresponds element leftWidth rightWidth,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements element leftWidth rightWidth

end Silean.Modules.VectorConcat
