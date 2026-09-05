import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.TupleField.TupleField

namespace Silean.Modules.TupleField

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

private def splitter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

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

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure signals field children)
    (cycleContract signals field)
    (stateCorresponds signals field children) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    children, inputs, structuralState, proposal, satisfies
  have splitMatches := childMatch .split
  have splitValue := ((splitter signals).outputRule_holds_iff _ _ _).mp
    (splitMatches.1.1 Composition.SignalComponentRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (selectRule signals field).Holds inputs contractState _
    rw [selectRule_holds_iff signals field]
    dsimp only
    change proposal.1 .field = _
    let selected := fun (values : (splitter signals).ports.outputs.Values) =>
      signals.typeAt_tuplePosition field ▸
        (show (signals.tupleFields.typeAt
          (signals.tuplePosition field)).Denote from
            values (signals.tuplePosition field))
    calc
      proposal.1 .field =
          ((body signals field).wiring.moduleOutput .field).value inputs
            (fun name => (proposal.2 name).outputs) := boundary .field
      _ = selected (proposal.2 .split).outputs := by
        exact outputSourceValue signals field inputs
          (fun name => (proposal.2 name).outputs)
      _ = selected ((splitter signals).outputValues
          (ProposedValues.childInputs (body signals field)
            (fun name => (children name).moduleStructure) inputs proposal.2 .split)) :=
        congrArg selected splitValue
      _ = selectedValue signals field (inputs .tuple) := by rfl
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
