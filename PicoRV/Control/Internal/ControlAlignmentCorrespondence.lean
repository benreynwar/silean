import PicoRV.Control.ControlAlignment
import PicoRV.Control.Internal.ControlAlignmentStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing alignment description
and its expanded typed production structure. -/

namespace PicoRV.Control.Alignment.Internal

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
  simp [circuit_description, enumeration, Alignment.wordSplitter,
    childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals rfl

theorem description_corresponds : Corresponds description Alignment.naming :=
  ⟨same⟩

end PicoRV.Control.Alignment.Internal
