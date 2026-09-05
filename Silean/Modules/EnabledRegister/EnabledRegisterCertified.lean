import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.Mux.MuxCertified

namespace Silean.Modules.EnabledRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-! ## Cycle certification -/

module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  selection := Modules.Mux.certification signalType,
  storage := Modules.Register.implementation signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .observe => [.storage => Primitives.RegisterRule.observe]
  state := [.storage => Primitives.RegisterRule.observe,
    .selection => Mux.Rule.select]

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : ChildStructures (body signalType) (childContracts signalType))

private def stateCorresponds
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches :=
    childSolutionMatchesContract layerChildren inputs structuralState proposal
      satisfies .storage contractState corresponds
  letI : Subsingleton (childContracts signalType .selection).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have selectionMatches :=
    childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState proposal satisfies .selection SignalMap.emptyValues
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (childContracts signalType .storage).stateRule.apply
      (ProposedValues.childInputs (body signalType)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage) contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType).Holds inputs contractState _
    rw [observeRule_holds_iff signalType]
    have boundaryOutput := boundary .q
    change outputs .q = (childProposals .storage).outputs .output at boundaryOutput
    exact boundaryOutput.trans ((Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have storageNextValue : storageNextState .stored =
        (ProposedValues.childInputs (body signalType)
          (fun child => (layerChildren child).moduleStructure)
          inputs childProposals .storage) .input := by
      rfl
    have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .data
        else (childProposals .storage).outputs .output at selected
    have storageCurrent := (Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    simp only [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.apply]
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .data else contractState .stored
    rw [selected, storageCurrent]

end LayerCertification

/-! The enabled-register wiring implements its contract for any mux and
register implementations satisfying their public contracts. -/
module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements signalType

end Silean.Modules.EnabledRegister
