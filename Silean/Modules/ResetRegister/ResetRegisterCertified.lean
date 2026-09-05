import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.ResetRegister.ResetRegister
import Silean.Modules.Mux.MuxCertified

namespace Silean.Modules.ResetRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue where
  resetValue := Constant.certification signalType resetValue,
  selection := Mux.certification signalType,
  storage := Register.implementation signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  output | .observe => [.storage => Primitives.RegisterRule.observe]
  state := [.resetValue => Primitives.ConstantRule.apply,
    .selection => Mux.Rule.select,
    .storage => Primitives.RegisterRule.observe]

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
  have statelessChildState (child : Instance)
      (h : child = .resetValue ∨ child = .selection) :
      Subsingleton (childContracts signalType resetValue child).state.Values := by
    rcases h with rfl | rfl <;>
      change Subsingleton emptySignalMap.Values <;> infer_instance
  have constantMatches :=
    letI := statelessChildState .resetValue (Or.inl rfl)
    childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .resetValue SignalMap.emptyValues
  have selectionMatches :=
    letI := statelessChildState .selection (Or.inr rfl)
    childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .selection SignalMap.emptyValues
  have storageMatches := childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .storage contractState corresponds
  rcases constantMatches with ⟨constantEvaluates, _⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases proposal with ⟨outputs, childProposals⟩
  let nextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
      (ProposedValues.childInputs (body signalType resetValue)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage) contractState
  refine ⟨nextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType resetValue).Holds inputs contractState _
    rw [observeRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((Register.outputRule_holds_iff signalType _ _ _).mp
        (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    have constantValue := (Constant.outputRule_holds_iff signalType resetValue _ _ _).mp
      (constantEvaluates.1 Primitives.ConstantRule.apply)
    have storageNextValue : nextState .stored =
        (ProposedValues.childInputs (body signalType resetValue)
          (fun child => (layerChildren child).moduleStructure)
          inputs childProposals .storage) .input := by
      rfl
    change (childProposals .selection).outputs .result =
      bif inputs .reset then
        (childProposals .resetValue).outputs .output else inputs .value at selected
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (childProposals .selection).outputs .result =
      bif inputs .reset then resetValue else inputs .value
    rw [selected, constantValue]

end LayerCertification

/- The reset-register wiring implements its contract using only the public
contracts of its constant, mux, and register children. -/
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

end Silean.Modules.ResetRegister
