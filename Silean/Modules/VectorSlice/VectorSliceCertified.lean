import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSlice.VectorSlice

namespace Silean.Modules.VectorSlice

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (element : SignalType)
    (prefixWidth : Nat) (width : Nat) (suffixWidth : Nat)
    for body element prefixWidth width suffixWidth where
  split := (splitter element prefixWidth width suffixWidth).certified.certification,
  combine := (combiner element width).certified.certification

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (prefixWidth : Nat) (width : Nat) (suffixWidth : Nat)
    for body element prefixWidth width suffixWidth
    with childContracts element prefixWidth width suffixWidth
    implementing cycleContract element prefixWidth width suffixWidth where
  output | .apply => [
    .split => Composition.SignalComponentRule.apply,
    .combine => Composition.SignalComponentRule.apply]
  state := []

section LayerCertification

variable (element : SignalType) (prefixWidth width suffixWidth : Nat)
  (layerChildren : (child : (instancePorts element prefixWidth width suffixWidth).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element prefixWidth width suffixWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element prefixWidth width suffixWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element prefixWidth width suffixWidth layerChildren).State) :
    Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure element prefixWidth width suffixWidth layerChildren)
    (cycleContract element prefixWidth width suffixWidth)
    (stateCorresponds element prefixWidth width suffixWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have childMatch (child : Instance) := by
    letI : Subsingleton
        ((childContracts element prefixWidth width suffixWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState (ProposedValues.composite outputs proposals) satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have splitOutputs : (proposals .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        (fun | .value => inputs .value) := by
    have held := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element prefixWidth width suffixWidth) _ _ _).mp
      ((childMatch .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs
        (body element prefixWidth width suffixWidth) _ inputs proposals .split =
          (fun | .value => inputs .value) := by
      funext input; cases input; rfl
    change (proposals .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        (ProposedValues.childInputs (body element prefixWidth width suffixWidth) _
          inputs proposals .split) at held
    rw [inputsEqual] at held
    exact held
  have combineOutputs : (proposals .combine).outputs =
      (combiner element width).outputValues
        (ProposedValues.childInputs (body element prefixWidth width suffixWidth) _
          inputs proposals .combine) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .combine).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = slice (inputs .value)
    rw [show outputs .result = (proposals .combine).outputs .value by
      exact satisfies.1 .result]
    rw [congrFun combineOutputs .value]
    funext index
    change (proposals .split).outputs
      (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) = _
    rw [splitOutputs]
    rfl
  · rfl

end LayerCertification

module_cycle_certification certification (element : SignalType)
    (prefixWidth : Nat) (width : Nat) (suffixWidth : Nat)
    for moduleStructure element prefixWidth width suffixWidth
    via body element prefixWidth width suffixWidth
    with childContracts element prefixWidth width suffixWidth
    implementing cycleContract element prefixWidth width suffixWidth where
  schedules := derivedRuleSchedules element prefixWidth width suffixWidth,
  structuralChildren := structuralChildren element prefixWidth width suffixWidth,
  certifiedChildren := certifiedChildren element prefixWidth width suffixWidth,
  structuresMatch := certifiedChildren_moduleStructure element prefixWidth width suffixWidth,
  stateCorresponds := stateCorresponds element prefixWidth width suffixWidth,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements element prefixWidth width suffixWidth

end Silean.Modules.VectorSlice
