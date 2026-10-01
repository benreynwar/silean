import PicoRV.Control.ControlExecuteTransition
import PicoRV.Control.Internal.ControlExecuteTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing execute-transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.ExecuteTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming ExecuteTransition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ExecuteTransition.moduleStructure ExecuteTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ExecuteTransition.body, ExecuteTransition.context,
    ExecuteTransition.instancePorts,
    ExecuteTransition.structuralChildren, ExecuteTransition.wiring,
    sourceDescription, Silean.Modules.Constant.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds : Corresponds description ExecuteTransition.naming :=
  ⟨same⟩

end PicoRV.Control.ExecuteTransition.Internal
