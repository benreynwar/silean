import PicoRV.Datapath.DatapathNext
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.Next.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Next.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Next.moduleStructure Next.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Next.body, Next.context, Next.instancePorts, Next.structuralChildren,
    Next.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]
    at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal | equal | equal | equal |
      equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description Next.naming :=
  ⟨same, unique⟩

end PicoRV.Datapath.Next.Description.Internal
