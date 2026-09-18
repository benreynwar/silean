import PicoRV.Decoder
import PicoRV.Decoder.DecoderCaptureStageTheorems
import PicoRV.Decoder.DecoderResolveStageTheorems
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules

namespace PicoRV.Decoder

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

/-! The parent proof composes the concrete certifications of both registered
decoder stages. The resolve stage depends only on the public contracts of its
three smaller, concrete combinational children. -/

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
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop :=
  (layerChildren .capture).certification.stateCorresponds
      (captureState contractState) (structuralState .capture) ∧
    (layerChildren .resolve).certification.stateCorresponds
      (resolveState contractState) (structuralState .resolve)

private theorem hasCorrespondingState
    (structuralState :
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .capture).certification.hasCorrespondingState
      (structuralState .capture) with ⟨capture, captureCorresponds⟩
  rcases (layerChildren .resolve).certification.hasCorrespondingState
      (structuralState .resolve) with ⟨resolve, resolveCorresponds⟩
  refine ⟨mergeState capture resolve, ?_⟩
  exact ⟨by simpa using captureCorresponds, by simpa using resolveCorresponds⟩

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have captureMatches := childSolutionMatchesContract layerChildren hierStep
    satisfies .capture (captureState contractState) corresponds.1
  have resolveMatches := childSolutionMatchesContract layerChildren hierStep
    satisfies .resolve (resolveState contractState) corresponds.2
  have captureOutputs : hierStep.childOutputs .capture = captureState contractState := by
    have allowed := captureMatches.allowed
    change CaptureStage.cycleContract.Allows _ at allowed
    exact CaptureStage.outputs_of_allowed allowed
  have resolveInputsEqual : ResolveStage.valuesOf
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .resolve) =
        resolveInputs (valuesOf hierStep.inputs) (captureState contractState) := by
    simp [ResolveStage.valuesOf, resolveInputs, valuesOf, wiring, context,
      instancePorts, Silean.EndpointContext.moduleInput,
      Silean.EndpointContext.instanceOutput, Silean.SignalSource.value, captureOutputs]
  have resolveOutputs : hierStep.childOutputs .resolve =
      ResolveStage.outputValues (resolveInputs (valuesOf hierStep.inputs)
        (captureState contractState)) (resolveState contractState) := by
    have allowed := resolveMatches.allowed
    change ResolveStage.cycleContract.Allows _ at allowed
    have held := ResolveStage.outputs_of_allowed allowed
    have result := held.trans (congrArg (fun inputs => ResolveStage.outputValues
      inputs (resolveState contractState)) resolveInputsEqual)
    normalize_child_contract result
  have captureNext :
      (childContracts .capture).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
            .capture) (captureState contractState) =
        CaptureStage.nextState (captureInputs (valuesOf hierStep.inputs))
          (captureState contractState) := by
    have allowed := captureMatches.allowed
    change CaptureStage.cycleContract.Allows _ at allowed
    exact CaptureStage.nextState_of_allowed allowed
  have resolveNext :
      (childContracts .resolve).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
            .resolve) (resolveState contractState) =
        ResolveStage.nextState
          (resolveInputs (valuesOf hierStep.inputs) (captureState contractState))
          (resolveState contractState) := by
    have allowed := resolveMatches.allowed
    change ResolveStage.cycleContract.Allows _ at allowed
    have held := ResolveStage.nextState_of_allowed allowed
    have result := held.trans (congrArg (fun inputs => ResolveStage.nextState
      inputs (resolveState contractState)) resolveInputsEqual)
    normalize_child_contract result
  let next := nextState (valuesOf hierStep.inputs) contractState
  refine ⟨next, ?_, ?_⟩
  · constructor
    · intro rule
      dsimp only
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary := satisfies.1 output
      cases output <;>
        simp only [wiring, context, Silean.EndpointContext.instanceOutput,
          Silean.SignalSource.value] at boundary <;>
        first
        | exact boundary.trans ((congrFun captureOutputs _).trans rfl)
        | exact boundary.trans ((congrFun resolveOutputs _).trans rfl)
    · change next = nextState (valuesOf hierStep.inputs) contractState
      rfl
  · constructor
    · change (layerChildren .capture).certification.stateCorresponds
        (captureState next)
          (Silean.HierStep.nextState (layerChildren .capture).moduleStructure
            (hierStep.children .capture))
      rw [show captureState next =
          CaptureStage.nextState (captureInputs (valuesOf hierStep.inputs))
            (captureState contractState) by simp [next, nextState]]
      rw [← captureNext]
      exact captureMatches.nextCorresponds
    · change (layerChildren .resolve).certification.stateCorresponds
        (resolveState next)
          (Silean.HierStep.nextState (layerChildren .resolve).moduleStructure
            (hierStep.children .resolve))
      rw [show resolveState next = ResolveStage.nextState
          (resolveInputs (valuesOf hierStep.inputs) (captureState contractState))
          (resolveState contractState) by simp [next, nextState]]
      rw [← resolveNext]
      exact resolveMatches.nextCorresponds

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

end PicoRV.Decoder
