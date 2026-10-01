import PicoRV.Memory.MemoryResponse
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing memory-response
description and its expanded typed production structure. -/

namespace PicoRV.Memory.Response.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Response.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Response.moduleStructure Response.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Response.body, Response.context, Response.instancePorts,
    Response.structuralChildren, Response.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem corresponds : Corresponds description Response.naming :=
  ⟨same⟩

end PicoRV.Memory.Response.Description.Internal
