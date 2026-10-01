import PicoRV.Control.ControlLoadRs2Transition
import PicoRV.Control.Internal.ControlLoadRs2TransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing load-RS2 transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.LoadRs2Transition.Internal

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

theorem description_corresponds : Corresponds description LoadRs2Transition.naming :=
  ⟨same⟩

end PicoRV.Control.LoadRs2Transition.Internal
