import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.Fifo.FifoPointerControl

/-! Checked correspondence between the reader-facing FIFO pointer-control
description and its expanded typed production structure. This is separate from
cycle verification so the two independent checks remain small compilation
units. -/

namespace Silean.Modules.Fifo.PointerControl.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (addressWidth : Nat) :
  some (description addressWidth) =
      ofNaming (PointerControl.naming addressWidth) := by
  simp only [circuit_description, description, construction,
    PointerControl.pointerSplitter, PointerControl.addressCombiner]
  simp [circuit_description, enumeration]
  rfl

private theorem unique (addressWidth : Nat) :
    (description addressWidth).UniqueNames := by
  simp only [circuit_description, description, construction,
    PointerControl.pointerSplitter, PointerControl.addressCombiner]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal | equal
  · subst child
    constructor
    · exact Naming.SignalAdapter.vectorSplitter_portNames_nodup
        (addressWidth + 1) .bit
    · exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Naming.SignalAdapter.vectorSplitter_portNames_nodup
        (addressWidth + 1) .bit
    · exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Naming.SignalAdapter.vectorCombiner_portNames_nodup
        addressWidth .bit
    · rw [List.map_map]
      change (Naming.SignalAdapter.combiner
        (.vector addressWidth .bit)).ports.inputs.names.Nodup
      exact (List.nodup_append.mp
        (Naming.SignalAdapter.vectorCombiner_portNames_nodup
          addressWidth .bit)).1
  · subst child
    constructor
    · exact Naming.SignalAdapter.vectorCombiner_portNames_nodup
        addressWidth .bit
    · rw [List.map_map]
      change (Naming.SignalAdapter.combiner
        (.vector addressWidth .bit)).ports.inputs.names.Nodup
      exact (List.nodup_append.mp
        (Naming.SignalAdapter.vectorCombiner_portNames_nodup
          addressWidth .bit)).1
  · subst child
    constructor
    · exact Equality.Naming.portNames_nodup (addressType addressWidth)
    · rw [Equality.Naming.naming_ports]
      exact of_decide_eq_true rfl
  all_goals subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds (addressWidth : Nat) :
    Corresponds (description addressWidth)
      (PointerControl.naming addressWidth) :=
  ⟨same addressWidth, unique addressWidth⟩

end Silean.Modules.Fifo.PointerControl.Description.Internal
