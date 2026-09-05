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
    Contracts.Cycle.Implements
      (certificationStructure element leftWidth rightWidth layerChildren)
      (cycleContract element leftWidth rightWidth)
      (stateCorresponds element leftWidth rightWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have boundary := satisfies.1
  have childMatch (child : (instancePorts element leftWidth rightWidth).Name) := by
    letI : Subsingleton
        ((childContracts element leftWidth rightWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs
        structuralState (ProposedValues.composite outputs proposals) satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have leftOutputs : (proposals .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues (leftInputs inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (leftSplitter element leftWidth) _ _ _).mp
      ((childMatch .leftSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth)
        (fun name => (layerChildren name).moduleStructure) inputs proposals
          .leftSplit = leftInputs inputs := by funext input; cases input; rfl
    change (proposals .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth)
          (fun name => (layerChildren name).moduleStructure) inputs proposals
          .leftSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have rightOutputs : (proposals .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues (rightInputs inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (rightSplitter element rightWidth) _ _ _).mp
      ((childMatch .rightSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth)
        (fun name => (layerChildren name).moduleStructure) inputs proposals
          .rightSplit = rightInputs inputs := by funext input; cases input; rfl
    change (proposals .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth)
          (fun name => (layerChildren name).moduleStructure) inputs proposals
          .rightSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have combineOutputs : (proposals .combine).outputs =
      (combiner element leftWidth rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .combine) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .combine).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = concat (inputs .left) (inputs .right)
    rw [show outputs .result = (proposals .combine).outputs .value by
      exact boundary .result]
    rw [congrFun combineOutputs .value]
    rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
        inputs proposals .combine =
          combineInputs (proposals .leftSplit).outputs
            (proposals .rightSplit).outputs by
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro leftIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]
      · intro rightIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]]
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
