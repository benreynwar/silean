import PicoRV.Datapath.DatapathNext
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.Next.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Next.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Next.moduleStructure Next.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Next.body, Next.context, Next.instancePorts, Next.structuralChildren,
    Next.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals rfl

theorem corresponds : Corresponds description Next.naming :=
  ⟨same⟩

end PicoRV.Datapath.Next.Description.Internal
