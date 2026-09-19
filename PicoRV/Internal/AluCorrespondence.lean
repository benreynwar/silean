import PicoRV.Alu
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the readable ALU dataflow and its expanded
typed production hierarchy. -/

namespace PicoRV.Alu.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Alu.naming := by
  simp only [circuit_description, description, construction]
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
        Source.child (.indexed "bit_mux" 6)
          (Silean.Modules.BitMux.naming.ports.outputs.name .result)
      else
        Source.child (.indexed "constant" 0)
          ((Silean.Modules.Constant.Naming.portsWithNaming .bit
            (.positional .bit)).outputs.name .output))
    (isSource := by
      intro index
      by_cases zero : index = 0 <;> simp [zero])]
  simp [circuit_description, enumeration]
  intro index _
  by_cases zero : index = 0 <;> simp [zero]

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration,
    Silean.Modules.Equality.design,
    Silean.Modules.Equality.Naming.naming_ports,
    Silean.Modules.BitwiseXor.Naming.namingWith_ports,
    Silean.Modules.BitwiseOr.Naming.namingWith_ports,
    Silean.Modules.BitwiseAnd.Naming.namingWith_ports]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal
  all_goals subst child
  all_goals constructor
  all_goals first
    | exact Silean.Modules.Equality.Naming.portNames_nodup wordType
    | exact Silean.Modules.BitwiseXor.Naming.portNames_nodup wordType
    | exact Silean.Modules.BitwiseOr.Naming.portNames_nodup wordType
    | exact Silean.Modules.BitwiseAnd.Naming.portNames_nodup wordType
    | exact of_decide_eq_true rfl

theorem corresponds : Corresponds description Alu.naming :=
  ⟨same, unique⟩

end PicoRV.Alu.Description.Internal
