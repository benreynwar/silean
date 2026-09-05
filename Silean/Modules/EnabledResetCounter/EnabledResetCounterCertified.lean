import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.EnabledResetCounter.EnabledResetCounter
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterCertified

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat)
    (resetValue : Value width) for body width resetValue where
  increment := Increment.certification width,
  storage := EnabledResetRegister.certification (valueType width) resetValue

module_rule_schedules derivedRuleSchedules (width : Nat)
    (resetValue : Value width) for body width resetValue
    with childContracts width resetValue
    implementing cycleContract width resetValue where
  output | .observe => [.storage => EnabledResetRegister.Rule.observe]
  state := [.storage => EnabledResetRegister.Rule.observe,
    .increment => Increment.Rule.apply]

section LayerCertification

variable (width : Nat) (resetValue : Value width)
  (layerChildren : ChildStructures (body width resetValue)
    (childContracts width resetValue))

private def stateCorresponds
    (contractState : (cycleContract width resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body width resetValue) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width resetValue) layerChildren)
      (cycleContract width resetValue)
      (stateCorresponds width resetValue layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .storage contractState corresponds
  letI : Subsingleton (childContracts width resetValue .increment).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have incrementMatches := childSolutionMatchesContract_of_subsingletonState
    layerChildren inputs structuralState proposal satisfies
    .increment SignalMap.emptyValues
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases incrementMatches with ⟨incrementEvaluates, _⟩
  let storageNextState :=
    (childContracts width resetValue .storage).stateRule.apply
      (ProposedValues.childInputs (body width resetValue)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage) contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule width).Holds inputs contractState outputs
    rw [outputRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((EnabledResetRegister.observeRule_holds_iff (valueType width) resetValue _ _ _).mp
        (storageEvaluates.1 EnabledResetRegister.Rule.observe))
  · have storageNextValue : storageNextState .stored =
        bif inputs .reset then resetValue
        else bif inputs .enable then childProposals .increment |>.outputs .result
          else contractState .stored := by
      exact EnabledResetRegister.stateRule_apply_stored
        (valueType width) resetValue _ _
    have incremented := Increment.result_of_evaluatesTo width _ _ _ _
      incrementEvaluates
    change (childProposals .increment).outputs .result =
      Increment.incrementValue width ((childProposals .storage).outputs .value)
      at incremented
    have storageCurrent :=
      (EnabledResetRegister.observeRule_holds_iff (valueType width) resetValue _ _ _).mp
        (storageEvaluates.1 EnabledResetRegister.Rule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif inputs .reset then resetValue
      else bif inputs .enable then (childProposals .increment).outputs .result
        else contractState .stored) =
      nextValue width resetValue (inputs .enable) (inputs .reset)
        (contractState .stored)
    rw [incremented, storageCurrent]
    rfl

end LayerCertification

/- The counter wiring implements its contract using only the public contracts
and certifications of its incrementer and storage children. -/
module_cycle_certification certification (width : Nat)
    (resetValue : Value width)
    for moduleStructure width resetValue via body width resetValue
    with childContracts width resetValue
    implementing cycleContract width resetValue where
  schedules := derivedRuleSchedules width resetValue,
  structuralChildren := structuralChildren width resetValue,
  certifiedChildren := certifiedChildren width resetValue,
  structuresMatch := certifiedChildren_moduleStructure width resetValue,
  stateCorresponds := stateCorresponds width resetValue,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements width resetValue

end Silean.Modules.EnabledResetCounter
