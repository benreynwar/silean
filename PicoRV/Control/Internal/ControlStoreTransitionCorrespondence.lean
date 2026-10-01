import PicoRV.Control.ControlStoreTransition
import PicoRV.Control.Internal.ControlStoreTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing Store-transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.StoreTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming StoreTransition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold StoreTransition.moduleStructure StoreTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [StoreTransition.body, StoreTransition.context,
    StoreTransition.instancePorts, StoreTransition.structuralChildren,
    StoreTransition.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description StoreTransition.naming :=
  ⟨same⟩

end PicoRV.Control.StoreTransition.Internal
