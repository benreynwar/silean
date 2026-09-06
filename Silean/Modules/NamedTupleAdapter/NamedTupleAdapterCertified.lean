import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Modules.NamedTupleCombiner

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signals : SignalMap)
    for body signals where
  adapter := (adapter signals).certified.certification

module_rule_schedules derivedRuleSchedules (signals : SignalMap)
    for body signals with childContracts signals implementing cycleContract signals where
  output | .apply => [.adapter => Composition.SignalComponentRule.apply]
  state := []

section LayerCertification

variable (signals : SignalMap)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts signals child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signals) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure signals layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure signals layerChildren) (cycleContract signals)
    (stateCorresponds signals layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    ((childMatch .adapter).1.1 Composition.SignalComponentRule.apply)
  have childInputsEqual :
      ProposedValues.childInputs (body signals)
          (fun name => (layerChildren name).moduleStructure)
          inputs proposal.2 .adapter =
        signals.allSelection.valueAt inputs := by
    funext position
    exact adapterInputValue signals inputs
      (fun name => (proposal.2 name).outputs) position
  rw [childInputsEqual] at childValue
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change proposal.outputs .value =
      signals.tupleFields.assemble (signals.allSelection.valueAt inputs)
    exact (boundary .value).trans (congrFun childValue .value)
  · rfl

end LayerCertification

module_cycle_certification certification (signals : SignalMap)
    for moduleStructure signals via body signals with childContracts signals
    implementing cycleContract signals where
  schedules := derivedRuleSchedules signals,
  structuralChildren := structuralChildren signals,
  certifiedChildren := certifiedChildren signals,
  structuresMatch := certifiedChildren_moduleStructure signals,
  stateCorresponds := stateCorresponds signals,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signals

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signals : SignalMap)
    for body signals where
  adapter := (adapter signals).certified.certification

module_rule_schedules derivedRuleSchedules (signals : SignalMap)
    for body signals with childContracts signals implementing cycleContract signals where
  output | .apply => [.adapter => Composition.SignalComponentRule.apply]
  state := []

section LayerCertification

variable (signals : SignalMap)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts signals child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signals) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure signals layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure signals layerChildren) (cycleContract signals)
    (stateCorresponds signals layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    ((childMatch .adapter).1.1 Composition.SignalComponentRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext label
    let selected := fun (values : (adapter signals).ports.outputs.Values) =>
      signals.typeAt_tuplePosition label ▸
        (show (signals.tupleFields.typeAt
          (signals.tuplePosition label)).Denote from
            values (signals.tuplePosition label))
    calc
      proposal.1 label =
          ((body signals).wiring.moduleOutput label).value inputs
            (fun name => (proposal.2 name).outputs) := boundary label
      _ = selected (proposal.2 .adapter).outputs := by
        exact moduleOutputValue signals inputs
          (fun name => (proposal.2 name).outputs) label
      _ = selected ((adapter signals).outputValues
          (ProposedValues.childInputs (body signals)
            (fun name => (layerChildren name).moduleStructure)
            inputs proposal.2 .adapter)) :=
        congrArg selected childValue
      _ = splitValue signals (inputs .value) label := by rfl
  · rfl

end LayerCertification

module_cycle_certification certification (signals : SignalMap)
    for moduleStructure signals via body signals with childContracts signals
    implementing cycleContract signals where
  schedules := derivedRuleSchedules signals,
  structuralChildren := structuralChildren signals,
  certifiedChildren := certifiedChildren signals,
  structuresMatch := certifiedChildren_moduleStructure signals,
  stateCorresponds := stateCorresponds signals,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signals

end Silean.Modules.NamedTupleSplitter
