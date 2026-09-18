import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Modules.NamedTupleCombiner

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

private theorem adapterInputValue (signals : SignalMap)
    (inputs : (ports signals).inputs.Values)
    (childOutputs : (name : (instancePorts signals).Name) →
      ((instancePorts signals).ports name).outputs.Values)
    (position : SignalTypes.Position signals.tupleFields) :
    ((wiring signals).instanceInput .adapter position).value inputs childOutputs =
      signals.allSelection.valueAt inputs position := by
  change (SignalSource.castType
    (signals.allSelection.signalType_labelAt position).symm
    ((context signals).moduleInput
      (signals.allSelection.labelAt position))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  exact signals.allSelection.cast_labelAt_value inputs position

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

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure signals layerChildren) (cycleContract signals)
    (stateCorresponds signals layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body signals from
    layerChildren, hierStep, satisfies
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    ((childMatch .adapter).ruleHolds Composition.SignalComponentRule.apply)
  have childInputsEqual :
      (body signals).wiring.childInputValues hierStep.inputs
          hierStep.childOutputs .adapter =
        signals.allSelection.valueAt hierStep.inputs := by
    funext position
    exact adapterInputValue signals hierStep.inputs
      hierStep.childOutputs position
  rw [childInputsEqual] at childValue
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .value =
      signals.tupleFields.assemble (signals.allSelection.valueAt hierStep.inputs)
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

private theorem moduleOutputValue (signals : SignalMap)
    (inputs : (ports signals).inputs.Values)
    (childOutputs : (name : (instancePorts signals).Name) →
      ((instancePorts signals).ports name).outputs.Values)
    (label : signals.Label) :
    ((wiring signals).moduleOutput label).value inputs childOutputs =
      signals.typeAt_tuplePosition label ▸
        childOutputs .adapter (signals.tuplePosition label) := by
  change (SignalSource.castType (signals.typeAt_tuplePosition label)
    ((context signals).instanceOutput .adapter
      (signals.tuplePosition label))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  rfl

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

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure signals layerChildren) (cycleContract signals)
    (stateCorresponds signals layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body signals from
    layerChildren, hierStep, satisfies
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    ((childMatch .adapter).ruleHolds Composition.SignalComponentRule.apply)
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
      hierStep.outputs label =
          ((body signals).wiring.moduleOutput label).value hierStep.inputs
            hierStep.childOutputs := boundary label
      _ = selected (hierStep.children .adapter).outputs := by
        exact moduleOutputValue signals hierStep.inputs
          hierStep.childOutputs label
      _ = selected ((adapter signals).outputValues
          ((body signals).wiring.childInputValues hierStep.inputs
            hierStep.childOutputs .adapter)) :=
        congrArg selected childValue
      _ = splitValue signals (hierStep.inputs .value) label := by rfl
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
