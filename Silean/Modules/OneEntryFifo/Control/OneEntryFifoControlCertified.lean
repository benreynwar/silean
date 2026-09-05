import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControl
import Silean.Primitives.Eq
import Silean.Primitives.Not
import Silean.Primitives.Or

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

private theorem implements : Contracts.Cycle.Implements
    (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
    cycleContract (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatches from
    layerChildren, inputs, structuralState, proposal, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change controlRule.Holds inputs contractState proposal.outputs
    rw [controlRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    have invertEvaluates := (childMatches .invertValid).1
    have readyEvaluates := (childMatches .readyOr).1
    have updateEvaluates := (childMatches .updateEq).1
    have invertOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have readyOutput := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (readyEvaluates.1 Primitives.OrRule.apply)
    have updateOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
      (updateEvaluates.1 Primitives.EqRule.apply)
    have readyEq : outputs .upstreamReady =
        (children .readyOr).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using
          boundary Output.upstreamReady
    have updateEq : outputs .storageUpdate =
        (children .updateEq).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using
          boundary Output.storageUpdate
    have invertEq : (children .invertValid).outputs .output =
        !inputs .storedValid := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, SignalSource.value] using invertOutput
    have readyChild : (children .readyOr).outputs .output =
        (inputs .downstreamReady || (children .invertValid).outputs .output) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using readyOutput
    have updateChild : (children .updateEq).outputs .output =
        ((inputs .downstreamReady && inputs .storedValid) ||
          (!inputs .downstreamReady && !inputs .storedValid)) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, SignalSource.value] using updateOutput
    constructor
    · exact readyEq.trans (readyChild.trans
        (congrArg (fun value => inputs .downstreamReady || value) invertEq))
    · exact updateEq.trans updateChild
  · rfl

end LayerCertification

/- The control wiring implements its contract using only the public contracts
of its three primitive children. -/
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
