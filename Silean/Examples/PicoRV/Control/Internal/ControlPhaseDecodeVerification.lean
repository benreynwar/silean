import Silean.Examples.PicoRV.Control.ControlPhaseDecode
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems

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

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have trapValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trap).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp trapValue unfolding wiring, context
  have fetchValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetch).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp fetchValue unfolding wiring, context
  have loadRs1Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs1Value unfolding wiring, context
  have loadRs2Value := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs2) _ _ _).mp
    ((childMatch .loadRs2).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadRs2Value unfolding wiring, context
  have executeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .execute).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp executeValue unfolding wiring, context
  have shiftValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shift).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp shiftValue unfolding wiring, context
  have storeValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .store).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp storeValue unfolding wiring, context
  have loadValue := (Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .load).ruleHolds Modules.EqualsConstant.Rule.apply)
  normalize_child_hyp loadValue unfolding wiring, context

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Control.PhaseDecode
