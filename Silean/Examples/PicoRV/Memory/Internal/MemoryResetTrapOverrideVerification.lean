import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Memory.ResetTrapOverride

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  capturedFields := Modules.NamedTupleSplitter.certification stateMap,
  notResetn := Primitives.notCertified.certification,
  resetOrTrap := Primitives.orCertified.certification,
  clearValid := Primitives.orCertified.certification,
  falseBit := Modules.Constant.certification .bit false,
  idleState := Modules.Constant.certification (.vector 2 .bit) (stateOfNat 0),
  overridePhase := Modules.Mux.certification (.vector 2 .bit),
  overrideValid := Modules.Mux.certification .bit,
  overrideValue := Modules.NamedTupleCombiner.certification stateMap,
  selected := Modules.Mux.certification stateType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .capturedFields} => Modules.NamedTupleSplitter.Rule.apply,
    .notResetn => Primitives.NotRule.apply,
    {.resetOrTrap, .clearValid} => Primitives.OrRule.apply,
    {.falseBit, .idleState} => Primitives.ConstantRule.apply,
    {.overridePhase, .overrideValid} => Modules.Mux.Rule.select,
    .overrideValue => Modules.NamedTupleCombiner.Rule.apply,
    .selected => Modules.Mux.Rule.select]
  state := []

def overrideResult (memoryInputs : Inputs) (captured : stateMap.Values) :
    stateMap.Values
  | .mem_state => bif memoryInputs.resetn
      then captured .mem_state else stateOfNat 0
  | .mem_valid => bif !memoryInputs.resetn || memoryInputs.mem_ready
      then false else captured .mem_valid
  | field => captured field

def structuralResult (memoryInputs : Inputs) (captured normal : stateMap.Values) :
    stateMap.Values :=
  bif !memoryInputs.resetn || memoryInputs.trap
    then overrideResult memoryInputs captured else normal

theorem structuralResult_eq_resetTrapApplied (memoryInputs : Inputs)
    (captured normal : stateMap.Values) :
    structuralResult memoryInputs captured normal =
      resetTrapApplied memoryInputs captured normal := by
  cases resetn : memoryInputs.resetn <;> cases trap : memoryInputs.trap <;>
    cases ready : memoryInputs.mem_ready <;> funext field <;> cases field <;>
    simp [structuralResult, overrideResult, resetTrapApplied, resetn, trap, ready,
      SignalMap.set]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let captured := stateMap.unpack (inputs .captured)
  let normal := stateMap.unpack (inputs .normal)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have capturedFieldsValue : hierStep.childOutputs .capturedFields = captured := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .capturedFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, captured] using equation
  have fieldValue (field : MemoryInputs.Field) :
      hierStep.childOutputs .inputsFields field = memoryInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have notResetValue : hierStep.childOutputs .notResetn .output =
      !memoryInputs.resetn := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notResetn).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .resetn] at equation
    exact equation
  have resetOrTrapValue : hierStep.childOutputs .resetOrTrap .output =
      (!memoryInputs.resetn || memoryInputs.trap) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .resetOrTrap).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [notResetValue, fieldValue .trap] at equation
    exact equation
  have clearValidValue : hierStep.childOutputs .clearValid .output =
      (!memoryInputs.resetn || memoryInputs.mem_ready) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .clearValid).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [notResetValue, fieldValue .mem_ready] at equation
    exact equation
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Primitives.ConstantRule.apply)
  have idleValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
    ((childMatch .idleState).ruleHolds Primitives.ConstantRule.apply)
  have phaseValue : hierStep.childOutputs .overridePhase .result =
      bif memoryInputs.resetn then captured .mem_state else stateOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .overridePhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .resetn, capturedFieldsValue, idleValue] at equation
    exact equation
  have validValue : hierStep.childOutputs .overrideValid .result =
      bif !memoryInputs.resetn || memoryInputs.mem_ready
        then false else captured .mem_valid := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .overrideValid).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [clearValidValue, capturedFieldsValue, falseValue] at equation
    exact equation

  have overrideInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .overrideValue = overrideResult memoryInputs captured := by
    funext field
    cases field
    · change hierStep.childOutputs .overridePhase .result = _; exact phaseValue
    · change hierStep.childOutputs .overrideValid .result = _; exact validValue
    · change hierStep.childOutputs .capturedFields .mem_instr = _
      exact congrFun capturedFieldsValue .mem_instr
    · change hierStep.childOutputs .capturedFields .mem_addr = _
      exact congrFun capturedFieldsValue .mem_addr
    · change hierStep.childOutputs .capturedFields .mem_wdata = _
      exact congrFun capturedFieldsValue .mem_wdata
    · change hierStep.childOutputs .capturedFields .mem_wstrb = _
      exact congrFun capturedFieldsValue .mem_wstrb
    · change hierStep.childOutputs .capturedFields .mem_rdata_q = _
      exact congrFun capturedFieldsValue .mem_rdata_q
  have overrideValue : hierStep.childOutputs .overrideValue .value =
      stateMap.pack (overrideResult memoryInputs captured) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .overrideValue).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [overrideInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have selectedValue : hierStep.childOutputs .selected .result =
      stateMap.pack (structuralResult memoryInputs captured normal) := by
    have equation := Modules.Mux.result_of_allowed stateType
      (childMatch .selected).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [resetOrTrapValue, overrideValue] at equation
    change hierStep.childOutputs .selected .result =
      bif !memoryInputs.resetn || memoryInputs.trap
        then stateMap.pack (overrideResult memoryInputs captured)
        else stateMap.pack normal at equation
    cases selected : (!memoryInputs.resetn || memoryInputs.trap) <;>
      simp [selected, structuralResult] at equation ⊢
    all_goals exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .selected .result by
      exact satisfies.1 .state]
    rw [selectedValue, structuralResult_eq_resetTrapApplied]
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

end Silean.Examples.PicoRV.Memory.ResetTrapOverride
