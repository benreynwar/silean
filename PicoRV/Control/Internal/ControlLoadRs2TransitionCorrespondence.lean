import PicoRV.Control.ControlLoadRs2Transition
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing load-RS2 transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.LoadRs2Transition.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming LoadRs2Transition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold LoadRs2Transition.moduleStructure LoadRs2Transition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [LoadRs2Transition.body, LoadRs2Transition.context,
    LoadRs2Transition.instancePorts,
    LoadRs2Transition.structuralChildren, LoadRs2Transition.wiring,
    sourceDescription, Silean.Modules.Constant.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description LoadRs2Transition.naming :=
  ⟨same, unique⟩

end PicoRV.Control.LoadRs2Transition.Description.Internal
