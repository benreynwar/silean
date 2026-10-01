import PicoRV.Decoder.DecoderImmediate
import PicoRV.Decoder.Internal.DecoderImmediateStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Decoder.Immediate.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Immediate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Immediate.moduleStructure Immediate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Immediate.body, Immediate.context, Immediate.instancePorts,
    Immediate.structuralChildren, Immediate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description Immediate.naming :=
  ⟨same⟩

end PicoRV.Decoder.Immediate.Internal
