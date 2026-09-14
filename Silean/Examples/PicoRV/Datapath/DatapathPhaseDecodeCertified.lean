import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantCertified

namespace Silean.Examples.PicoRV.Datapath.PhaseDecode

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  fetchMatch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  loadRs1Match := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  loadRs2Match := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs2),
  executeMatch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shiftMatch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeMatch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  loadMatch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .fetchMatch => Modules.EqualsConstant.Rule.apply,
        .loadRs1Match => Modules.EqualsConstant.Rule.apply,
        .loadRs2Match => Modules.EqualsConstant.Rule.apply,
        .executeMatch => Modules.EqualsConstant.Rule.apply,
        .shiftMatch => Modules.EqualsConstant.Rule.apply,
        .storeMatch => Modules.EqualsConstant.Rule.apply,
        .loadMatch => Modules.EqualsConstant.Rule.apply]
  state := []

private theorem signalTypeEqualOfNat (width value : Nat)
    (bits : Fin width → Bool) (bound : value < 2 ^ width) :
    (SignalType.vector width .bit).equal bits (BitVector.ofNat width value) =
      decide (BitVector.toNat width bits = value) := by
  have encoded : BitVector.toNat width (BitVector.ofNat width value) = value := by
    rw [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : BitVector.toNat width bits = value
  · have bitsEqual : bits = BitVector.ofNat width value := by
      apply BitVector.toNat_injective width
      simpa [encoded] using matched
    rw [((SignalType.vector width .bit).equal_eq_true_iff _ _).mpr bitsEqual]
    simp [matched]
  · have bitsDifferent : bits ≠ BitVector.ofNat width value := by
      intro equal
      apply matched
      rw [equal, encoded]
    simp only [matched]
    cases left : (SignalType.vector width .bit).equal bits
        (BitVector.ofNat width value)
    · rfl
    · exact (bitsDifferent
        (((SignalType.vector width .bit).equal_eq_true_iff _ _).mp left)).elim

private theorem equalStateBits (bits : Fin 8 → Bool) (value : Nat)
    (bound : value < 256) :
    (SignalType.vector 8 .bit).equal bits (stateBits value) =
      decide (BitVector.toNat 8 bits = value) := by
  have representation : stateBits value = BitVector.ofNat 8 value := by
    funext index
    simp [stateBits, BitVector.ofNat]
  rw [representation]
  exact signalTypeEqualOfNat 8 value bits (by simpa using bound)

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

  have fetchValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp fetchValue unfolding body, wiring, context
  have loadRs1Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1Match).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs1Value unfolding body, wiring, context
  have loadRs2Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs2) _ _ _).mp
    ((childMatch .loadRs2Match).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs2Value unfolding body, wiring, context
  have executeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .executeMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp executeValue unfolding body, wiring, context
  have shiftValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shiftMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp shiftValue unfolding body, wiring, context
  have storeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .storeMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp storeValue unfolding body, wiring, context
  have loadValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .loadMatch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadValue unfolding body, wiring, context

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output
    · rw [show proposal.outputs .fetch =
          (proposal.2 .fetchMatch).outputs .result by exact satisfies.1 .fetch]
      rw [fetchValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .loadRs1 =
          (proposal.2 .loadRs1Match).outputs .result by exact satisfies.1 .loadRs1]
      rw [loadRs1Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .loadRs2 =
          (proposal.2 .loadRs2Match).outputs .result by exact satisfies.1 .loadRs2]
      rw [loadRs2Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .execute =
          (proposal.2 .executeMatch).outputs .result by exact satisfies.1 .execute]
      rw [executeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .shift =
          (proposal.2 .shiftMatch).outputs .result by exact satisfies.1 .shift]
      rw [shiftValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .store =
          (proposal.2 .storeMatch).outputs .result by exact satisfies.1 .store]
      rw [storeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .load =
          (proposal.2 .loadMatch).outputs .result by exact satisfies.1 .load]
      rw [loadValue, equalStateBits _ _ (by decide)]
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

end Silean.Examples.PicoRV.Datapath.PhaseDecode
