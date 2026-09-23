import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.ROM.Internal.ROMStructure

/-! Certification of the constant-table and mux-tree ROM implementation. -/

namespace Silean.Modules.ROM

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (definitionName : String)
    (element : SignalType) (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    for body definitionName element addressWidth contents where
  contents := Constant.certification
    (.vector (entryCount addressWidth) element) contents,
  select := CombMuxTree.certification element addressWidth

module_rule_schedules derivedRuleSchedules (definitionName : String)
    (element : SignalType) (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    for body definitionName element addressWidth contents
    with childContracts definitionName element addressWidth contents
    implementing cycleContract element addressWidth contents where
  output | .read => [
    .contents => Primitives.ConstantRule.apply,
    .select => CombMuxTree.Rule.apply]
  state := []

section LayerCertification

variable (definitionName : String) (element : SignalType) (addressWidth : Nat)
  (contents : Fin (entryCount addressWidth) → element.Denote)
  (layerChildren :
    (child : (instancePorts definitionName element addressWidth contents).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (childContracts definitionName element addressWidth contents child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body definitionName element addressWidth contents) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure definitionName element addressWidth contents
      layerChildren).State) : Prop :=
  True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure definitionName element addressWidth contents
      layerChildren)
    (cycleContract element addressWidth contents)
    (stateCorresponds definitionName element addressWidth contents
      layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for
    body definitionName element addressWidth contents from
      layerChildren, hierStep, satisfies
  have contentsOutput :
      (hierStep.children .contents).outputs .output = contents :=
    Constant.output_of_allowed
      (.vector (entryCount addressWidth) element) contents
      (childMatch .contents).allowed
  have selectInputs :
      (body definitionName element addressWidth contents).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .select =
        (fun
          | .values => (hierStep.children .contents).outputs .output
          | .index => hierStep.inputs .address) := by
    funext input
    cases input <;> rfl
  have selectOutput :
      (hierStep.children .select).outputs .result =
        CombMuxTree.select addressWidth
          ((hierStep.children .contents).outputs .output)
          (hierStep.inputs .address) := by
    have held := CombMuxTree.cycleContract.result element addressWidth
      (childMatch .select).allowed
    change (hierStep.children .select).outputs .result =
      CombMuxTree.select addressWidth
        (((body definitionName element addressWidth contents).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .select) .values)
        (((body definitionName element addressWidth contents).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .select) .index) at held
    rw [selectInputs] at held
    exact held
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [readRule_holds_iff]
    change hierStep.outputs .data =
      lookup addressWidth contents (hierStep.inputs .address)
    rw [show hierStep.outputs .data =
        (hierStep.children .select).outputs .result by
      exact satisfies.1 .data]
    rw [selectOutput, contentsOutput]
    rfl
  · rfl

end LayerCertification

module_cycle_certification certification (definitionName : String)
    (element : SignalType) (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    for moduleStructure definitionName element addressWidth contents
    via body definitionName element addressWidth contents
    with childContracts definitionName element addressWidth contents
    implementing cycleContract element addressWidth contents where
  schedules := derivedRuleSchedules definitionName element addressWidth contents,
  structuralChildren := structuralChildren definitionName element addressWidth contents,
  certifiedChildren := certifiedChildren definitionName element addressWidth contents,
  structuresMatch := certifiedChildren_moduleStructure
    definitionName element addressWidth contents,
  stateCorresponds := stateCorresponds
    definitionName element addressWidth contents,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements definitionName element addressWidth contents

end Silean.Modules.ROM
