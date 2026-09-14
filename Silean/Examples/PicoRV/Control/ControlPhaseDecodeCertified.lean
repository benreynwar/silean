import Silean.Examples.PicoRV.Control.ControlPhaseDecode
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantCertified

namespace Silean.Examples.PicoRV.Control.PhaseDecode

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  trap := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  fetch := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  loadRs1 := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  loadRs2 := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs2),
  execute := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shift := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  store := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  load := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .trap => Modules.EqualsConstant.Rule.apply,
        .fetch => Modules.EqualsConstant.Rule.apply,
        .loadRs1 => Modules.EqualsConstant.Rule.apply,
        .loadRs2 => Modules.EqualsConstant.Rule.apply,
        .execute => Modules.EqualsConstant.Rule.apply,
        .shift => Modules.EqualsConstant.Rule.apply,
        .store => Modules.EqualsConstant.Rule.apply,
        .load => Modules.EqualsConstant.Rule.apply]
  state := []

private theorem equalStateBits (bits : Fin 8 → Bool) (value : Nat)
    (bound : value < 256) :
    (SignalType.vector 8 .bit).equal bits (stateBits value) =
      decide (BitVector.toNat 8 bits = value) := by
  have representation : stateBits value = BitVector.ofNat 8 value := by
    funext index
    simp [stateBits, BitVector.ofNat]
  rw [representation]
  exact signalTypeEqual_ofNat 8 value bits (by simpa using bound)

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

  have trapValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trap).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp trapValue unfolding body, wiring, context
  have fetchValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetch).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp fetchValue unfolding body, wiring, context
  have loadRs1Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs1Value unfolding body, wiring, context
  have loadRs2Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs2) _ _ _).mp
    ((childMatch .loadRs2).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs2Value unfolding body, wiring, context
  have executeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .execute).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp executeValue unfolding body, wiring, context
  have shiftValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shift).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp shiftValue unfolding body, wiring, context
  have storeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .store).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp storeValue unfolding body, wiring, context
  have loadValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .load).1.1 Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadValue unfolding body, wiring, context

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output
    · rw [show proposal.outputs .trap = (proposal.2 .trap).outputs .result by
        exact satisfies.1 .trap]
      rw [trapValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .fetch = (proposal.2 .fetch).outputs .result by
        exact satisfies.1 .fetch]
      rw [fetchValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .loadRs1 = (proposal.2 .loadRs1).outputs .result by
        exact satisfies.1 .loadRs1]
      rw [loadRs1Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .loadRs2 = (proposal.2 .loadRs2).outputs .result by
        exact satisfies.1 .loadRs2]
      rw [loadRs2Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .execute = (proposal.2 .execute).outputs .result by
        exact satisfies.1 .execute]
      rw [executeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .shift = (proposal.2 .shift).outputs .result by
        exact satisfies.1 .shift]
      rw [shiftValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .store = (proposal.2 .store).outputs .result by
        exact satisfies.1 .store]
      rw [storeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show proposal.outputs .load = (proposal.2 .load).outputs .result by
        exact satisfies.1 .load]
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

end Silean.Examples.PicoRV.Control.PhaseDecode
