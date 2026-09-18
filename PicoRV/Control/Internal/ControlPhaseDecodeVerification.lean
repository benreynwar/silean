import PicoRV.Control.ControlPhaseDecode
import PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems

namespace PicoRV.Control.PhaseDecode

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  trap := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  fetch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  loadRs1 := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  loadRs2 := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs2),
  execute := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shift := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  store := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  load := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .trap => Silean.Modules.EqualsConstant.Rule.apply,
        .fetch => Silean.Modules.EqualsConstant.Rule.apply,
        .loadRs1 => Silean.Modules.EqualsConstant.Rule.apply,
        .loadRs2 => Silean.Modules.EqualsConstant.Rule.apply,
        .execute => Silean.Modules.EqualsConstant.Rule.apply,
        .shift => Silean.Modules.EqualsConstant.Rule.apply,
        .store => Silean.Modules.EqualsConstant.Rule.apply,
        .load => Silean.Modules.EqualsConstant.Rule.apply]
  state := []

private theorem equalStateBits (bits : Fin 8 → Bool) (value : Nat)
    (bound : value < 256) :
    (Silean.SignalType.vector 8 .bit).equal bits (stateBits value) =
      decide (Silean.BitVector.toNat 8 bits = value) := by
  have representation : stateBits value = Silean.BitVector.ofNat 8 value := by
    funext index
    simp [stateBits, Silean.BitVector.ofNat]
  rw [representation]
  exact signalTypeEqual_ofNat 8 value bits (by simpa using bound)

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have trapValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trap).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp trapValue unfolding wiring, context
  have fetchValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp fetchValue unfolding wiring, context
  have loadRs1Value := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs1Value unfolding wiring, context
  have loadRs2Value := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs2) _ _ _).mp
    ((childMatch .loadRs2).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs2Value unfolding wiring, context
  have executeValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .execute).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp executeValue unfolding wiring, context
  have shiftValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shift).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp shiftValue unfolding wiring, context
  have storeValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .store).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp storeValue unfolding wiring, context
  have loadValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .load).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadValue unfolding wiring, context

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    funext output
    cases output
    · rw [show hierStep.outputs .trap = hierStep.childOutputs .trap .result by
        exact satisfies.1 .trap]
      exact trapValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .fetch = hierStep.childOutputs .fetch .result by
        exact satisfies.1 .fetch]
      exact fetchValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .loadRs1 = hierStep.childOutputs .loadRs1 .result by
        exact satisfies.1 .loadRs1]
      exact loadRs1Value.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .loadRs2 = hierStep.childOutputs .loadRs2 .result by
        exact satisfies.1 .loadRs2]
      exact loadRs2Value.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .execute = hierStep.childOutputs .execute .result by
        exact satisfies.1 .execute]
      exact executeValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .shift = hierStep.childOutputs .shift .result by
        exact satisfies.1 .shift]
      exact shiftValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .store = hierStep.childOutputs .store .result by
        exact satisfies.1 .store]
      exact storeValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
    · rw [show hierStep.outputs .load = hierStep.childOutputs .load .result by
        exact satisfies.1 .load]
      exact loadValue.trans (by
        rw [equalStateBits _ _ (by decide)]
        rfl)
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Control.PhaseDecode
