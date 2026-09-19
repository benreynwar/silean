import PicoRV.Control.ControlCommandFinish
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing command-finishing
description and its expanded typed production structure. -/

namespace PicoRV.Control.CommandFinish.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming CommandFinish.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold CommandFinish.moduleStructure CommandFinish.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [CommandFinish.body, CommandFinish.context,
    CommandFinish.instancePorts, CommandFinish.structuralChildren,
    CommandFinish.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description CommandFinish.naming :=
  ⟨same, unique⟩

end PicoRV.Control.CommandFinish.Description.Internal
