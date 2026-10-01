import PicoRV.Control.ControlFetchTransition
import PicoRV.Control.Internal.ControlFetchTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing Fetch-transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.FetchTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming FetchTransition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold FetchTransition.moduleStructure FetchTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [FetchTransition.body, FetchTransition.context,
    FetchTransition.instancePorts, FetchTransition.structuralChildren,
    FetchTransition.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description FetchTransition.naming :=
  ⟨same⟩

end PicoRV.Control.FetchTransition.Internal
