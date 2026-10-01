import PicoRV.Control.ControlLoadTransition
import PicoRV.Control.Internal.ControlLoadTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing Load-transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.LoadTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming LoadTransition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold LoadTransition.moduleStructure LoadTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [LoadTransition.body, LoadTransition.context,
    LoadTransition.instancePorts, LoadTransition.structuralChildren,
    LoadTransition.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals rfl

theorem description_corresponds : Corresponds description LoadTransition.naming :=
  ⟨same⟩

end PicoRV.Control.LoadTransition.Internal
