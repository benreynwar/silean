import PicoRV.Control.ControlTrapTransition
import PicoRV.Control.Internal.ControlTrapTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Control.TrapTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming TrapTransition.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold TrapTransition.moduleStructure TrapTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [TrapTransition.body, TrapTransition.context,
    TrapTransition.instancePorts, TrapTransition.structuralChildren,
    TrapTransition.wiring, sourceDescription, Silean.Modules.Constant.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds : Corresponds description TrapTransition.naming :=
  ⟨same⟩

end PicoRV.Control.TrapTransition.Internal
