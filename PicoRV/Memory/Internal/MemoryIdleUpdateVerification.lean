import PicoRV.Memory.MemoryBasicUpdates
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.Or

namespace PicoRV.Memory.IdleUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  instructionCommand := Silean.Primitives.orCertified.certification,
  readCommand := Silean.Primitives.orCertified.certification,
  trueBit := Silean.Modules.Constant.certification .bit true,
  falseBit := Silean.Modules.Constant.certification .bit false,
  zeroMask := Silean.Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0),
  readState := Silean.Modules.Constant.certification (.vector 2 .bit) (stateOfNat 1),
  writeState := Silean.Modules.Constant.certification (.vector 2 .bit) (stateOfNat 2),
  readValid := Silean.Modules.BitMux.certification,
  readInstr := Silean.Modules.BitMux.certification,
  readMask := Silean.Modules.Mux.certification (.vector 4 .bit),
  readPhase := Silean.Modules.Mux.certification (.vector 2 .bit),
  finalValid := Silean.Modules.BitMux.certification,
  finalInstr := Silean.Modules.BitMux.certification,
  finalPhase := Silean.Modules.Mux.certification (.vector 2 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .instructionCommand => Silean.Primitives.OrRule.apply,
    .readCommand => Silean.Primitives.OrRule.apply,
    {.trueBit, .falseBit, .zeroMask, .readState, .writeState} =>
      Silean.Primitives.ConstantRule.apply,
    {.readValid, .readInstr} => Silean.Modules.BitMux.Rule.select,
    {.readMask, .readPhase} => Silean.Modules.Mux.Rule.select,
    {.finalValid, .finalInstr} => Silean.Modules.BitMux.Rule.select,
    .finalPhase => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (memoryInputs : Inputs) (updated : stateMap.Values) :
    stateMap.Values :=
  let instruction := memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst
  let read := instruction || memoryInputs.mem_do_rdata
  fun
    | .mem_state => bif memoryInputs.mem_do_wdata then stateOfNat 2
        else bif read then stateOfNat 1 else updated .mem_state
    | .mem_valid => bif memoryInputs.mem_do_wdata then true
        else bif read then true else updated .mem_valid
    | .mem_instr => bif memoryInputs.mem_do_wdata then false
        else bif read then instruction else updated .mem_instr
    | .mem_wstrb => bif read then maskOfNat 0 else updated .mem_wstrb
    | field => updated field

theorem structuralResult_eq_idleNextState (memoryInputs : Inputs)
    (updated : stateMap.Values) :
    structuralResult memoryInputs updated = idleNextState memoryInputs updated := by
  cases prefetch : memoryInputs.mem_do_prefetch <;>
    cases rinst : memoryInputs.mem_do_rinst <;>
    cases rdata : memoryInputs.mem_do_rdata <;>
    cases wdata : memoryInputs.mem_do_wdata <;>
    funext field <;> cases field <;>
    simp [structuralResult, idleNextState, prefetch, rinst, rdata, wdata,
      Silean.SignalMap.set]

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

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have fieldValue (field : MemoryInputs.Field) :
      hierStep.childOutputs .inputsFields field = memoryInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have instructionValue : hierStep.childOutputs .instructionCommand .output =
      (memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .mem_do_prefetch, fieldValue .mem_do_rinst] at equation
    exact equation
  have readValue : hierStep.childOutputs .readCommand .output =
      (memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
        memoryInputs.mem_do_rdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .readCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [instructionValue, fieldValue .mem_do_rdata] at equation
    exact equation
  have trueValue := (Silean.Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have zeroMaskValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0) _ _ _).mp
    ((childMatch .zeroMask).ruleHolds Silean.Primitives.ConstantRule.apply)
  have readStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 1) _ _ _).mp
    ((childMatch .readState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have writeStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 2) _ _ _).mp
    ((childMatch .writeState).ruleHolds Silean.Primitives.ConstantRule.apply)

  have readValidValue : hierStep.childOutputs .readValid .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then true else updated .mem_valid := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .readValid).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [readValue, updatedFieldsValue, trueValue] at equation
    exact equation
  have readInstrValue : hierStep.childOutputs .readInstr .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata
        then memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst
        else updated .mem_instr := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .readInstr).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [readValue, updatedFieldsValue, instructionValue] at equation
    exact equation
  have readMaskValue : hierStep.childOutputs .readMask .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then maskOfNat 0 else updated .mem_wstrb := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .readMask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [readValue, updatedFieldsValue, zeroMaskValue] at equation
    exact equation
  have readPhaseValue : hierStep.childOutputs .readPhase .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then stateOfNat 1 else updated .mem_state := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .readPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [readValue, updatedFieldsValue, readStateValue] at equation
    exact equation
  have finalValidValue : hierStep.childOutputs .finalValid .result =
      bif memoryInputs.mem_do_wdata then true else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata then true else updated .mem_valid := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .finalValid).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .mem_do_wdata, readValidValue, trueValue] at equation
    exact equation
  have finalInstrValue : hierStep.childOutputs .finalInstr .result =
      bif memoryInputs.mem_do_wdata then false else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata
          then memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst
          else updated .mem_instr := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .finalInstr).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .mem_do_wdata, readInstrValue, falseValue] at equation
    exact equation
  have finalPhaseValue : hierStep.childOutputs .finalPhase .result =
      bif memoryInputs.mem_do_wdata then stateOfNat 2 else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata then stateOfNat 1 else updated .mem_state := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .finalPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fieldValue .mem_do_wdata, readPhaseValue, writeStateValue] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralResult memoryInputs updated := by
    funext field
    cases field
    · change hierStep.childOutputs .finalPhase .result = _; exact finalPhaseValue
    · change hierStep.childOutputs .finalValid .result = _; exact finalValidValue
    · change hierStep.childOutputs .finalInstr .result = _; exact finalInstrValue
    · change hierStep.childOutputs .updatedFields .mem_addr = _
      exact congrFun updatedFieldsValue .mem_addr
    · change hierStep.childOutputs .updatedFields .mem_wdata = _
      exact congrFun updatedFieldsValue .mem_wdata
    · change hierStep.childOutputs .readMask .result = _; exact readMaskValue
    · change hierStep.childOutputs .updatedFields .mem_rdata_q = _
      exact congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (structuralResult memoryInputs updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    rw [resultValue, structuralResult_eq_idleNextState]
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

end PicoRV.Memory.IdleUpdate
