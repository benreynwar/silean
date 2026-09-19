import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.ExecuteUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ExecuteUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ExecuteUpdate.moduleStructure ExecuteUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ExecuteUpdate.body, ExecuteUpdate.context,
    ExecuteUpdate.instancePorts, ExecuteUpdate.structuralChildren,
    ExecuteUpdate.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description ExecuteUpdate.naming :=
  ⟨same, unique⟩

end PicoRV.Datapath.ExecuteUpdate.Description.Internal
