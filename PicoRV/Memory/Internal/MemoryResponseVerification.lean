import PicoRV.Memory.MemoryResponse
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Memory.Response

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  transfer := Silean.Primitives.andCertified.certification,
  idle := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 0),
  nonIdle := Silean.Primitives.notCertified.certification,
  transferNonIdle := Silean.Primitives.andCertified.certification,
  readCommand := Silean.Primitives.orCertified.certification,
  activeCommand := Silean.Primitives.orCertified.certification,
  ordinaryCompletion := Silean.Primitives.andCertified.certification,
  prefetched := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 3),
  delayedCompletion := Silean.Primitives.andCertified.certification,
  completion := Silean.Primitives.orCertified.certification,
  enabledCompletion := Silean.Primitives.andCertified.certification,
  responseData := Silean.Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .done => [
        .currentFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .transfer => Silean.Primitives.AndRule.apply,
        .readCommand => Silean.Primitives.OrRule.apply,
        {.idle, .prefetched} => Silean.Modules.EqualsConstant.Rule.apply,
        .nonIdle => Silean.Primitives.NotRule.apply,
        .transferNonIdle => Silean.Primitives.AndRule.apply,
        .activeCommand => Silean.Primitives.OrRule.apply,
        {.ordinaryCompletion, .delayedCompletion} => Silean.Primitives.AndRule.apply,
        .completion => Silean.Primitives.OrRule.apply,
        .enabledCompletion => Silean.Primitives.AndRule.apply]
    | .data => [
        .currentFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .transfer => Silean.Primitives.AndRule.apply,
        .responseData => Silean.Modules.Mux.Rule.select]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let current := stateMap.unpack (inputs .current)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [Memory.ProofSupport.splitValue_eq_unpack, current] using equation
  have validValue : hierStep.childOutputs .currentFields .mem_valid =
      current .mem_valid := by rw [currentFieldsValue]
  have phaseValue : hierStep.childOutputs .currentFields .mem_state =
      current .mem_state := by rw [currentFieldsValue]
  have responseQValue : hierStep.childOutputs .currentFields .mem_rdata_q =
      current .mem_rdata_q := by rw [currentFieldsValue]

  have transferValue : hierStep.childOutputs .transfer .output =
      (current .mem_valid && inputs .mem_ready) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transfer).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [validValue] at equation
    exact equation
  have idleValue : hierStep.childOutputs .idle .result =
      decide (stateNumber current = 0) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
      ((childMatch .idle).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [phaseValue, Memory.ProofSupport.equal_stateOfNat _ _ (by decide)]
      at equation
    exact equation
  have nonIdleValue : hierStep.childOutputs .nonIdle .output =
      decide (stateNumber current ≠ 0) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .nonIdle).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [idleValue] at equation
    by_cases equal : stateNumber current = 0
    · simpa [equal] using equation
    · simpa [equal] using equation
  have transferNonIdleValue : hierStep.childOutputs .transferNonIdle .output =
      ((current .mem_valid && inputs .mem_ready) &&
        decide (stateNumber current ≠ 0)) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transferNonIdle).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [transferValue, nonIdleValue] at equation
    exact equation
  have readCommandValue : hierStep.childOutputs .readCommand .output =
      (inputs .mem_do_rinst || inputs .mem_do_rdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .readCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have activeCommandValue : hierStep.childOutputs .activeCommand .output =
      (inputs .mem_do_rinst || inputs .mem_do_rdata || inputs .mem_do_wdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .activeCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [readCommandValue] at equation
    exact equation
  have ordinaryValue : hierStep.childOutputs .ordinaryCompletion .output =
      ((current .mem_valid && inputs .mem_ready) &&
        decide (stateNumber current ≠ 0) &&
        (inputs .mem_do_rinst || inputs .mem_do_rdata || inputs .mem_do_wdata)) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .ordinaryCompletion).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [transferNonIdleValue, activeCommandValue] at equation
    exact equation
  have prefetchedValue : hierStep.childOutputs .prefetched .result =
      decide (stateNumber current = 3) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 3) _ _ _).mp
      ((childMatch .prefetched).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [phaseValue, Memory.ProofSupport.equal_stateOfNat _ _ (by decide)]
      at equation
    exact equation
  have delayedValue : hierStep.childOutputs .delayedCompletion .output =
      (decide (stateNumber current = 3) && inputs .mem_do_rinst) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .delayedCompletion).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [prefetchedValue] at equation
    exact equation
  have completionValue : hierStep.childOutputs .completion .output =
      (((current .mem_valid && inputs .mem_ready) &&
          decide (stateNumber current ≠ 0) &&
          (inputs .mem_do_rinst || inputs .mem_do_rdata || inputs .mem_do_wdata)) ||
        (decide (stateNumber current = 3) && inputs .mem_do_rinst)) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .completion).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [ordinaryValue, delayedValue] at equation
    exact equation
  have doneValue : hierStep.childOutputs .enabledCompletion .output =
      memDoneFrom (inputs .resetn) (inputs .mem_do_rinst)
        (inputs .mem_do_rdata) (inputs .mem_do_wdata) (inputs .mem_ready)
        current := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .enabledCompletion).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [completionValue] at equation
    simpa [memDoneFrom, stateNumber] using equation
  have responseValue : hierStep.childOutputs .responseData .result =
      memRdataLatchedFrom (inputs .mem_ready) (inputs .mem_rdata) current := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .responseData).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [transferValue, responseQValue] at equation
    cases valid : current .mem_valid <;> cases ready : inputs .mem_ready <;>
      simp [memRdataLatchedFrom, memXferFrom, valid, ready] at equation ⊢ <;>
      exact equation

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    dsimp only
    cases rule
    · rw [doneRule_holds_iff]
      rw [show hierStep.outputs .mem_done =
          hierStep.childOutputs .enabledCompletion .output by
        exact satisfies.1 .mem_done]
      simpa [Response.doneValue, current] using doneValue
    · rw [dataRule_holds_iff]
      rw [show hierStep.outputs .mem_rdata_latched =
          hierStep.childOutputs .responseData .result by
        exact satisfies.1 .mem_rdata_latched]
      simpa [current] using responseValue
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

end PicoRV.Memory.Response
