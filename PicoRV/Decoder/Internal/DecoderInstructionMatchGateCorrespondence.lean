import PicoRV.Decoder.DecoderInstructionMatchGate
import PicoRV.Decoder.Internal.DecoderInstructionMatchGateStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Decoder.InstructionMatch.MatchGate.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Structure.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Structure.moduleStructure Structure.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Structure.body, Structure.context, Structure.instancePorts,
    Structure.structuralChildren, Structure.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description Structure.naming :=
  ⟨same⟩

end PicoRV.Decoder.InstructionMatch.MatchGate.Internal
