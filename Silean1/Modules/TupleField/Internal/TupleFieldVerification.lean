import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.TupleField.TupleField
import Silean.Modules.TupleField.Internal.TupleFieldStructure

namespace Silean.Modules.TupleField

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

open Internal

private theorem outputSourceValue (signals : SignalMap) (field : signals.Label)
    (inputs : (ports signals field).inputs.Values)
    (childOutputs : (name : (instancePorts signals field).Name) →
      ((instancePorts signals field).ports name).outputs.Values) :
    ((body signals field).wiring.moduleOutput .field).value inputs childOutputs =
      signals.typeAt_tuplePosition field ▸
        (show (signals.tupleFields.typeAt
          (signals.tuplePosition field)).Denote from
          childOutputs .split (signals.tuplePosition field)) := by
  change (SignalSource.castType (signals.typeAt_tuplePosition field)
    ((context signals field).instanceOutput .split
      (signals.tuplePosition field))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  rfl

module_child_certifications childContracts (signals : SignalMap) (field : signals.Label)
    for body signals field where
  split := (splitter signals).certified.certification

module_rule_schedules derivedRuleSchedules (signals : SignalMap)
    (field : signals.Label) for body signals field
    with childContracts signals field implementing cycleContract signals field where
  output | .select => [.split => Composition.SignalComponentRule.apply]
  state := []

section

variable (signals : SignalMap) (field : signals.Label)
  (children : ChildStructures (body signals field) (childContracts signals field))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signals field) children

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure signals field children).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure signals field children)
    (cycleContract signals field)
    (stateCorresponds signals field children) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body signals field from
    children, hierStep, satisfies
  have splitMatches := childMatch .split
  have splitValue := ((splitter signals).outputRule_holds_iff _ _ _).mp
    (splitMatches.ruleHolds Composition.SignalComponentRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (selectRule signals field).Holds hierStep.inputs contractState _
    rw [selectRule_holds_iff signals field]
    dsimp only
    change hierStep.outputs .field = _
    let selected := fun (values : (splitter signals).ports.outputs.Values) =>
      signals.typeAt_tuplePosition field ▸
        (show (signals.tupleFields.typeAt
          (signals.tuplePosition field)).Denote from
            values (signals.tuplePosition field))
    calc
      hierStep.outputs .field =
          ((body signals field).wiring.moduleOutput .field).value hierStep.inputs
            hierStep.childOutputs := boundary .field
      _ = selected (hierStep.children .split).outputs := by
        exact outputSourceValue signals field hierStep.inputs
          hierStep.childOutputs
      _ = selected ((splitter signals).outputValues
          ((body signals field).wiring.childInputValues hierStep.inputs
            hierStep.childOutputs .split)) :=
        congrArg selected splitValue
      _ = selectedValue signals field (hierStep.inputs .tuple) := by rfl
  · rfl

end

module_cycle_certification certification (signals : SignalMap)
    (field : signals.Label) for moduleStructure signals field
    via body signals field with childContracts signals field
    implementing cycleContract signals field where
  schedules := derivedRuleSchedules signals field,
  structuralChildren := structuralChildren signals field,
  certifiedChildren := certifiedChildren signals field,
  structuresMatch := certifiedChildren_moduleStructure signals field,
  stateCorresponds := stateCorresponds signals field,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signals field

end Silean.Modules.TupleField
