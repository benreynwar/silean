import PicoRV.Decoder.Internal.DecoderResolveStageVerification

/-! Public resolve-stage declarations backed by generated internals. -/

namespace PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def place
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  placeIndexed "decoder_resolve_stage" design inputs

attribute [circuit_description] place

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Decoder.ResolveStage
