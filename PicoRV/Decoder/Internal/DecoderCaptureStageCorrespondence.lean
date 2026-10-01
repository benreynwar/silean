import PicoRV.Decoder.DecoderCaptureStage
import PicoRV.Decoder.Internal.DecoderCaptureStageStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Decoder.CaptureStage.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming CaptureStage.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold CaptureStage.moduleStructure CaptureStage.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [CaptureStage.body, CaptureStage.context, CaptureStage.instancePorts,
    CaptureStage.structuralChildren, CaptureStage.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description CaptureStage.naming :=
  ⟨same⟩

end PicoRV.Decoder.CaptureStage.Internal
