import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems

namespace PicoRV.Datapath.PhaseDecode

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  fetchMatch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  loadRs1Match := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  loadRs2Match := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs2),
  executeMatch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shiftMatch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeMatch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  loadMatch := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .fetchMatch => Silean.Modules.EqualsConstant.Rule.apply,
        .loadRs1Match => Silean.Modules.EqualsConstant.Rule.apply,
        .loadRs2Match => Silean.Modules.EqualsConstant.Rule.apply,
        .executeMatch => Silean.Modules.EqualsConstant.Rule.apply,
        .shiftMatch => Silean.Modules.EqualsConstant.Rule.apply,
        .storeMatch => Silean.Modules.EqualsConstant.Rule.apply,
        .loadMatch => Silean.Modules.EqualsConstant.Rule.apply]
  state := []

private theorem signalTypeEqualOfNat (width value : Nat)
    (bits : Fin width → Bool) (bound : value < 2 ^ width) :
    (Silean.SignalType.vector width .bit).equal bits (Silean.BitVector.ofNat width value) =
      decide (Silean.BitVector.toNat width bits = value) := by
  have encoded : Silean.BitVector.toNat width (Silean.BitVector.ofNat width value) = value := by
    rw [Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : Silean.BitVector.toNat width bits = value
  · have bitsEqual : bits = Silean.BitVector.ofNat width value := by
      apply Silean.BitVector.toNat_injective width
      simpa [encoded] using matched
    rw [((Silean.SignalType.vector width .bit).equal_eq_true_iff _ _).mpr bitsEqual]
    simp [matched]
  · have bitsDifferent : bits ≠ Silean.BitVector.ofNat width value := by
      intro equal
      apply matched
      rw [equal, encoded]
    simp only [matched]
    cases left : (Silean.SignalType.vector width .bit).equal bits
        (Silean.BitVector.ofNat width value)
    · rfl
    · exact (bitsDifferent
        (((Silean.SignalType.vector width .bit).equal_eq_true_iff _ _).mp left)).elim

private theorem equalStateBits (bits : Fin 8 → Bool) (value : Nat)
    (bound : value < 256) :
    (Silean.SignalType.vector 8 .bit).equal bits (stateBits value) =
      decide (Silean.BitVector.toNat 8 bits = value) := by
  have representation : stateBits value = Silean.BitVector.ofNat 8 value := by
    funext index
    simp [stateBits, Silean.BitVector.ofNat]
  rw [representation]
  exact signalTypeEqualOfNat 8 value bits (by simpa using bound)

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
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  have fetchValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchMatch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .fetchMatch .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateFetch) at fetchValue
  have loadRs1Value := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1Match).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .loadRs1Match .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateLdRs1) at loadRs1Value
  have loadRs2Value := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs2) _ _ _).mp
    ((childMatch .loadRs2Match).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .loadRs2Match .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateLdRs2) at loadRs2Value
  have executeValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .executeMatch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .executeMatch .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateExec) at executeValue
  have shiftValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shiftMatch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .shiftMatch .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateShift) at shiftValue
  have storeValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .storeMatch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .storeMatch .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateStmem) at storeValue
  have loadValue := (Silean.Modules.EqualsConstant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .loadMatch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
  change hierStep.childOutputs .loadMatch .result =
    (Silean.SignalType.vector 8 .bit).equal (hierStep.inputs .cpu_state)
      (stateBits cpuStateLdmem) at loadValue

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    funext output
    cases output
    · rw [show hierStep.outputs .fetch =
          hierStep.childOutputs .fetchMatch .result by exact satisfies.1 .fetch]
      rw [fetchValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .loadRs1 =
          hierStep.childOutputs .loadRs1Match .result by exact satisfies.1 .loadRs1]
      rw [loadRs1Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .loadRs2 =
          hierStep.childOutputs .loadRs2Match .result by exact satisfies.1 .loadRs2]
      rw [loadRs2Value, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .execute =
          hierStep.childOutputs .executeMatch .result by exact satisfies.1 .execute]
      rw [executeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .shift =
          hierStep.childOutputs .shiftMatch .result by exact satisfies.1 .shift]
      rw [shiftValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .store =
          hierStep.childOutputs .storeMatch .result by exact satisfies.1 .store]
      rw [storeValue, equalStateBits _ _ (by decide)]
      rfl
    · rw [show hierStep.outputs .load =
          hierStep.childOutputs .loadMatch .result by exact satisfies.1 .load]
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.PhaseDecode
