import PicoRV.Memory.MemoryReadFormatting
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing memory read-formatting
description and its expanded typed production structure. -/

namespace PicoRV.Memory.ReadFormatting.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming ReadFormatting.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ReadFormatting.moduleStructure ReadFormatting.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ReadFormatting.body, ReadFormatting.context,
    ReadFormatting.instancePorts, ReadFormatting.structuralChildren,
    ReadFormatting.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem corresponds : Corresponds description ReadFormatting.naming :=
  ⟨same⟩

end PicoRV.Memory.ReadFormatting.Description.Internal
