import PicoRV.Memory.Internal.MemoryLookaheadStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing memory look-ahead
description and its expanded typed production structure. -/

namespace PicoRV.Memory.Lookahead.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Lookahead.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Lookahead.moduleStructure Lookahead.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Lookahead.body, Lookahead.context, Lookahead.instancePorts,
    Lookahead.structuralChildren, Lookahead.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description Lookahead.naming :=
  ⟨same⟩

end PicoRV.Memory.Lookahead.Internal
