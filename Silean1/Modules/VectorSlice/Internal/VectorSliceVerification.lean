import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Modules.VectorSlice.Internal.VectorSliceStructure

namespace Silean.Modules.VectorSlice

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

open Internal

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

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure element prefixWidth width suffixWidth layerChildren)
    (cycleContract element prefixWidth width suffixWidth)
    (stateCorresponds element prefixWidth width suffixWidth layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch
    for body element prefixWidth width suffixWidth from
      layerChildren, hierStep, satisfies
  have splitOutputs : (hierStep.children .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        (fun | .value => hierStep.inputs .value) := by
    have held := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element prefixWidth width suffixWidth) _ _ _).mp
      ((childMatch .split).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (body element prefixWidth width suffixWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .split =
          (fun | .value => hierStep.inputs .value) := by
      funext input; cases input; rfl
    change (hierStep.children .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        ((body element prefixWidth width suffixWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .split) at held
    rw [inputsEqual] at held
    exact held
  have combineOutputs : (hierStep.children .combine).outputs =
      (combiner element width).outputValues
        ((body element prefixWidth width suffixWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .combine) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .combine).ruleHolds Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result = slice (hierStep.inputs .value)
    rw [show hierStep.outputs .result =
        (hierStep.children .combine).outputs .value by
      exact satisfies.1 .result]
    rw [congrFun combineOutputs .value]
    funext index
    change (hierStep.children .split).outputs
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
