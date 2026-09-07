import Silean.Examples.PicoRV.Decoder
import Silean.Examples.PicoRV.Decoder.DecoderCaptureStageCertified
import Silean.Examples.PicoRV.Decoder.DecoderResolveStageCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules

namespace Silean.Examples.PicoRV.Decoder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-! The parent proof composes the concrete certifications of both registered
decoder stages. The resolve stage itself depends only on the public contracts
of its three smaller combinational blackbox children. -/

module_child_certifications childContracts for body where
  capture := CaptureStage.certification,
  resolve := ResolveStage.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [.capture => CaptureStage.Rule.outputs,
      .resolve => ResolveStage.Rule.outputs]
  state := [.capture => CaptureStage.Rule.outputs,
    .resolve => ResolveStage.Rule.outputs]

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop :=
  (layerChildren .capture).certification.stateCorresponds
      (captureState contractState) (structuralState .capture) ∧
    (layerChildren .resolve).certification.stateCorresponds
      (resolveState contractState) (structuralState .resolve)

private theorem hasCorrespondingState
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .capture).certification.hasCorrespondingState
      (structuralState .capture) with ⟨capture, captureCorresponds⟩
  rcases (layerChildren .resolve).certification.hasCorrespondingState
      (structuralState .resolve) with ⟨resolve, resolveCorresponds⟩
  refine ⟨mergeState capture resolve, ?_⟩
  exact ⟨by simpa using captureCorresponds, by simpa using resolveCorresponds⟩

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have captureMatches := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .capture (captureState contractState) corresponds.1
  have resolveMatches := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .resolve (resolveState contractState) corresponds.2
  have captureOutputs : (proposal.2 .capture).outputs = captureState contractState :=
    (CaptureStage.outputRule_holds_iff _ _ _).mp
      (captureMatches.1.1 CaptureStage.Rule.outputs)
  have resolveOutputs : (proposal.2 .resolve).outputs =
      ResolveStage.outputValues (resolveInputs (valuesOf inputs)
        (captureState contractState)) (resolveState contractState) := by
    have held := (ResolveStage.outputRule_holds_iff _ _ _).mp
      (resolveMatches.1.1 ResolveStage.Rule.outputs)
    simpa [ResolveStage.valuesOf, resolveInputs, valuesOf,
      ProposedValues.childInputs_apply, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value, captureOutputs] using held
  have captureNext :
      (childContracts .capture).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .capture) (captureState contractState) =
        CaptureStage.nextState (captureInputs (valuesOf inputs))
          (captureState contractState) := by
    rfl
  have resolveNext :
      (childContracts .resolve).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .resolve) (resolveState contractState) =
        ResolveStage.nextState
          (resolveInputs (valuesOf inputs) (captureState contractState))
          (resolveState contractState) := by
    change ResolveStage.nextState
      (resolveInputs (valuesOf inputs) (proposal.2 .capture).outputs)
        (resolveState contractState) = _
    rw [captureOutputs]
  let next := nextState (valuesOf inputs) contractState
  refine ⟨next, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary : proposal.outputs output =
          (wiring.moduleOutput output).value inputs
            (fun child => (proposal.2 child).outputs) := by
        simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy] using
          satisfies.1 output
      cases output <;>
        simp only [wiring, context, EndpointContext.instanceOutput,
          SignalSource.value] at boundary <;>
        rw [boundary] <;>
        first
        | exact (congrFun captureOutputs _).trans rfl
        | exact (congrFun resolveOutputs _).trans rfl
    · change next = nextState (valuesOf inputs) contractState
      rfl
  · constructor
    · change (layerChildren .capture).certification.stateCorresponds
        (captureState next) (proposal.2 .capture).nextState
      rw [show captureState next =
          CaptureStage.nextState (captureInputs (valuesOf inputs))
            (captureState contractState) by simp [next, nextState]]
      rw [← captureNext]
      exact captureMatches.2
    · change (layerChildren .resolve).certification.stateCorresponds
        (resolveState next) (proposal.2 .resolve).nextState
      rw [show resolveState next = ResolveStage.nextState
          (resolveInputs (valuesOf inputs) (captureState contractState))
          (resolveState contractState) by simp [next, nextState]]
      rw [← resolveNext]
      exact resolveMatches.2

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := hasCorrespondingState,
  implements := implements

/- The generated `certified` bundle contains both concrete registered stages. -/

end Silean.Examples.PicoRV.Decoder
