import PicoRV.Decoder.Internal.DecoderCaptureStageVerification

/-! Public capture-stage declarations backed by generated internals. -/

namespace PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def place
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  placeIndexed "decoder_capture_stage" design inputs

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  Authoring.CircuitDescription.placeNamed name design inputs

attribute [circuit_description] place placeNamed

theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Decoder.CaptureStage
