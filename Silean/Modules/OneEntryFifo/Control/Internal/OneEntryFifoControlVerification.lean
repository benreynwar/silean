import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControl
import Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlStructure

/-! Certification machinery for the one-entry FIFO control child. -/

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  invertValid := Primitives.notCertified.certification,
  readyOr := Primitives.orCertified.certification,
  updateEq := Primitives.eqCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .control => [.invertValid => Primitives.NotRule.apply,
    .readyOr => Primitives.OrRule.apply,
    .updateEq => Primitives.EqRule.apply]
  state := []

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
    cycleContract (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatches for body from
    layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change controlRule.Holds hierStep.inputs contractState hierStep.outputs
    rw [controlRule_holds_iff]
    have invertOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatches .invertValid).ruleHolds Primitives.NotRule.apply)
    have readyOutput := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatches .readyOr).ruleHolds Primitives.OrRule.apply)
    have updateOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
      ((childMatches .updateEq).ruleHolds Primitives.EqRule.apply)
    normalize_child_hyp invertOutput unfolding wiring, context
    normalize_child_hyp readyOutput unfolding wiring, context
    normalize_child_hyp updateOutput unfolding wiring, context
    constructor
    · exact (boundary .upstreamReady).trans (readyOutput.trans
        (congrArg (fun value => hierStep.inputs .downstreamReady || value)
          invertOutput))
    · exact (boundary .storageUpdate).trans updateOutput
  · rfl

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Modules.OneEntryFifo.Control

namespace Silean.Modules.OneEntryFifo.Control.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same : some description = ofNaming Control.naming := by
  rfl

theorem description_corresponds : Corresponds description Control.naming :=
  ⟨same⟩

open Authoring.CircuitDescription.Description

theorem construction_correct :
    ImplementsCycleContract Control.description cycleContract Naming.ports := by
  have corresponds := description_corresponds
  unfold Control.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := { instancePorts := instancePorts, wiring := wiring })
    (children := structuralChildren)
    corresponds certification

end Silean.Modules.OneEntryFifo.Control.Internal
