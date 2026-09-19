import PicoRV.Control.ControlAlignment
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing alignment description
and its expanded typed production structure. -/

namespace PicoRV.Control.Alignment.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Alignment.naming := by
  simp only [circuit_description, description, construction,
    Silean.Modules.EqualsConstant.place]
  simp [circuit_description, enumeration]
  unfold Alignment.moduleStructure Alignment.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Alignment.body, Alignment.context, Alignment.instancePorts,
    Alignment.structuralChildren, Alignment.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, Alignment.wordSplitter]
  constructor <;> rfl

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction,
    Silean.Modules.EqualsConstant.place]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description Alignment.naming :=
  ⟨same, unique⟩

end PicoRV.Control.Alignment.Description.Internal
