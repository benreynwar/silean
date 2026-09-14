import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantCertified

namespace Silean.Examples.PicoRV.Memory.PhaseDecode

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  idleMatch := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 0),
  readMatch := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 1),
  writeMatch := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 2),
  prefetchedMatch := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 3)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.idleMatch, .readMatch, .writeMatch, .prefetchedMatch} =>
      Modules.EqualsConstant.Rule.apply]
  state := []

private theorem equalStateOfNat (bits : TwoBits) (value : Nat)
    (bound : value < 4) :
    (SignalType.vector 2 .bit).equal bits (stateOfNat value) =
      decide (BitVector.toNat 2 bits = value) := by
  have encoded : BitVector.toNat 2 (stateOfNat value) = value := by
    rw [show stateOfNat value = BitVector.ofNat 2 value by rfl]
    rw [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : BitVector.toNat 2 bits = value
  · have bitsEqual : bits = stateOfNat value := by
      apply BitVector.toNat_injective 2
      simpa [encoded] using matched
    rw [((SignalType.vector 2 .bit).equal_eq_true_iff _ _).mpr bitsEqual]
    simp [matched]
  · have bitsDifferent : bits ≠ stateOfNat value := by
      intro equal
      apply matched
      rw [equal, encoded]
    simp only [matched]
    cases left : (SignalType.vector 2 .bit).equal bits (stateOfNat value)
    · rfl
    · exact (bitsDifferent
        (((SignalType.vector 2 .bit).equal_eq_true_iff _ _).mp left)).elim

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  have idleValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
    ((childMatch .idleMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp idleValue unfolding body, wiring, context
  have readValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 1) _ _ _).mp
    ((childMatch .readMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp readValue unfolding body, wiring, context
  have writeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 2) _ _ _).mp
    ((childMatch .writeMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp writeValue unfolding body, wiring, context
  have prefetchedValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 3) _ _ _).mp
    ((childMatch .prefetchedMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp prefetchedValue unfolding body, wiring, context

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output
    · rw [show proposal.outputs .idle =
          (proposal.2 .idleMatch).outputs .result by exact satisfies.1 .idle]
      rw [idleValue, equalStateOfNat _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .read =
          (proposal.2 .readMatch).outputs .result by exact satisfies.1 .read]
      rw [readValue, equalStateOfNat _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .write =
          (proposal.2 .writeMatch).outputs .result by exact satisfies.1 .write]
      rw [writeValue, equalStateOfNat _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .prefetched =
          (proposal.2 .prefetchedMatch).outputs .result by
            exact satisfies.1 .prefetched]
      rw [prefetchedValue, equalStateOfNat _ _ (by decide)]
      rfl
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.PhaseDecode
