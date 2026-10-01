import PicoRV.Control.ControlCommandFinish
import PicoRV.Control.Internal.ControlCommandFinishStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing command-finishing
description and its expanded typed production structure. -/

namespace PicoRV.Control.CommandFinish.Internal

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
  simp [childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description CommandFinish.naming :=
  ⟨same⟩

end PicoRV.Control.CommandFinish.Internal
