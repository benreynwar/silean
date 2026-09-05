import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMux
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Modules.BitMux

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  invertSelect := Primitives.notCertified.certification,
  chooseFalse := Primitives.andCertified.certification,
  chooseTrue := Primitives.andCertified.certification,
  combine := Primitives.orCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .select => [.invertSelect => Primitives.NotRule.apply,
      .chooseFalse => Primitives.AndRule.apply,
      .chooseTrue => Primitives.AndRule.apply,
      .combine => Primitives.OrRule.apply]
  state := []

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have invertEvaluates := (childMatch .invertSelect).1
  have falseEvaluates := (childMatch .chooseFalse).1
  have trueEvaluates := (childMatch .chooseTrue).1
  have combineEvaluates := (childMatch .combine).1
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change selectRule.Holds inputs contractState _
    rcases proposal with ⟨outputs, children⟩
    have boundary' : outputs .result = (children .combine).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        instancePorts, EndpointContext.instanceOutput, SignalSource.value] using
          boundary Output.result
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (falseEvaluates.1 Primitives.AndRule.apply)
    have trueBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (trueEvaluates.1 Primitives.AndRule.apply)
    have combineBit := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (combineEvaluates.1 Primitives.OrRule.apply)
    change (children .invertSelect).outputs .output = !inputs .select at invertBit
    change (children .chooseFalse).outputs .output =
      (inputs .whenFalse && (children .invertSelect).outputs .output) at falseBit
    change (children .chooseTrue).outputs .output =
      (inputs .whenTrue && inputs .select) at trueBit
    change (children .combine).outputs .output =
      ((children .chooseFalse).outputs .output ||
        (children .chooseTrue).outputs .output) at combineBit
    rw [selectRule_holds_iff]
    simp only [ProposedValues.outputs]
    rw [boundary', combineBit, falseBit, trueBit, invertBit]
    cases inputs .select <;> cases inputs .whenFalse <;>
      cases inputs .whenTrue <;> rfl
  · rfl

end LayerCertification

/- The gate-level mux wiring implements its contract using only the public
contracts of its primitive children. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Modules.BitMux
