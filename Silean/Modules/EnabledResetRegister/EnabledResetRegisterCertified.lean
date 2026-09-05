import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.ResetRegister.ResetRegisterCertified

namespace Silean.Modules.EnabledResetRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue where
  selection := Mux.certification signalType,
  storage := ResetRegister.certification signalType resetValue

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  output | .observe => [.storage => ResetRegister.Rule.observe]
  state := [.storage => ResetRegister.Rule.observe,
    .selection => Mux.Rule.select]

section LayerCertification

variable (signalType : SignalType) (resetValue : signalType.Denote)
  (layerChildren : ChildStructures (body signalType resetValue)
    (childContracts signalType resetValue))

private def stateCorresponds
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType resetValue) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType resetValue) layerChildren)
      (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .storage contractState corresponds
  letI : Subsingleton (childContracts signalType resetValue .selection).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have selectionMatches := childSolutionMatchesContract_of_subsingletonState
    layerChildren inputs structuralState proposal satisfies
    .selection SignalMap.emptyValues
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
      (ProposedValues.childInputs (body signalType resetValue)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage) contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType resetValue).Holds inputs contractState _
    rw [observeRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((ResetRegister.observeRule_holds_iff signalType resetValue _ _ _).mp
        (storageEvaluates.1 ResetRegister.Rule.observe))
  · have storageNextValue : storageNextState .stored =
        bif inputs .reset then resetValue
        else (childProposals .selection).outputs .result := by
      exact ResetRegister.stateRule_apply_stored signalType resetValue _ _
    have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value
        else (childProposals .storage).outputs .value at selected
    have storageCurrent :=
      (ResetRegister.observeRule_holds_iff signalType resetValue _ _ _).mp
        (storageEvaluates.1 ResetRegister.Rule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif inputs .reset then resetValue
      else (childProposals .selection).outputs .result) =
      bif inputs .reset then resetValue
      else bif inputs .enable then inputs .value else contractState .stored
    rw [selected, storageCurrent]

end LayerCertification

/- The enabled-reset-register wiring implements its contract using only the
public contracts of its mux and reset-register children. -/
module_cycle_certification certification (signalType : SignalType)
    (resetValue : signalType.Denote)
    for moduleStructure signalType resetValue via body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  schedules := derivedRuleSchedules signalType resetValue,
  structuralChildren := structuralChildren signalType resetValue,
  certifiedChildren := certifiedChildren signalType resetValue,
  structuresMatch := certifiedChildren_moduleStructure signalType resetValue,
  stateCorresponds := stateCorresponds signalType resetValue,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements signalType resetValue

end Silean.Modules.EnabledResetRegister
