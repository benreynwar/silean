import PicoRV.Internal.AluStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the readable ALU dataflow and its expanded
typed production hierarchy. -/

namespace PicoRV.Alu.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Alu.naming := by
  simp (config := { maxSteps := 1000000 }) only
    [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Alu.moduleStructure Alu.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Alu.body, Alu.context, Alu.instancePorts, Alu.structuralChildren,
    Alu.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  rw [Internal.finalizeConnections_map_of_sources
    (source := fun index =>
      if index = 0 then
        Source.child { index := 21 }
          (portId Silean.Modules.BitMux.outputMap .result)
      else
        Source.child { index := 8 }
          (portId Silean.Primitives.singleOutputMap .output))
    (isSource := by
      intro index
      by_cases zero : index = 0 <;> simp [zero])]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro index _
       by_cases zero : index = 0 <;> simp [zero] <;>
         exact of_decide_eq_true rfl)

theorem description_corresponds : Corresponds description Alu.naming :=
  ⟨same⟩

end PicoRV.Alu.Internal
