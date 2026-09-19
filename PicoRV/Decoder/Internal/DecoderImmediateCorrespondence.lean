import PicoRV.Decoder.DecoderImmediate
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Decoder.Immediate.Description.Internal

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
  simp [circuit_description, enumeration]

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal | equal | equal | equal |
      equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description Immediate.naming :=
  ⟨same, unique⟩

end PicoRV.Decoder.Immediate.Description.Internal
