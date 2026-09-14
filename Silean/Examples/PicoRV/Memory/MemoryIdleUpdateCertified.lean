import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Memory.IdleUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  instructionCommand := Primitives.orCertified.certification,
  readCommand := Primitives.orCertified.certification,
  trueBit := Modules.Constant.certification .bit true,
  falseBit := Modules.Constant.certification .bit false,
  zeroMask := Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0),
  readState := Modules.Constant.certification (.vector 2 .bit) (stateOfNat 1),
  writeState := Modules.Constant.certification (.vector 2 .bit) (stateOfNat 2),
  readValid := Modules.Mux.certification .bit,
  readInstr := Modules.Mux.certification .bit,
  readMask := Modules.Mux.certification (.vector 4 .bit),
  readPhase := Modules.Mux.certification (.vector 2 .bit),
  finalValid := Modules.Mux.certification .bit,
  finalInstr := Modules.Mux.certification .bit,
  finalPhase := Modules.Mux.certification (.vector 2 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Modules.NamedTupleSplitter.Rule.apply,
    .instructionCommand => Primitives.OrRule.apply,
    .readCommand => Primitives.OrRule.apply,
    {.trueBit, .falseBit, .zeroMask, .readState, .writeState} =>
      Primitives.ConstantRule.apply,
    {.readValid, .readInstr, .readMask, .readPhase} => Modules.Mux.Rule.select,
    {.finalValid, .finalInstr, .finalPhase} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
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
      SignalMap.set]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralStateValue proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralStateValue, proposal, satisfies

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have fieldValue (field : MemoryInputs.Field) :
      (proposal.2 .inputsFields).outputs field = memoryInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have instructionValue : (proposal.2 .instructionCommand).outputs .output =
      (memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionCommand).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fieldValue .mem_do_prefetch, fieldValue .mem_do_rinst] at equation
    exact equation
  have readValue : (proposal.2 .readCommand).outputs .output =
      (memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
        memoryInputs.mem_do_rdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .readCommand).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instructionValue, fieldValue .mem_do_rdata] at equation
    exact equation
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have zeroMaskValue := (Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0) _ _ _).mp
    ((childMatch .zeroMask).1.1 Primitives.ConstantRule.apply)
  have readStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 1) _ _ _).mp
    ((childMatch .readState).1.1 Primitives.ConstantRule.apply)
  have writeStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 2) _ _ _).mp
    ((childMatch .writeState).1.1 Primitives.ConstantRule.apply)

  have readValidValue : (proposal.2 .readValid).outputs .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then true else updated .mem_valid := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .readValid).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [readValue, updatedFieldsValue, trueValue] at equation
    exact equation
  have readInstrValue : (proposal.2 .readInstr).outputs .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata
        then memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst
        else updated .mem_instr := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .readInstr).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [readValue, updatedFieldsValue, instructionValue] at equation
    exact equation
  have readMaskValue : (proposal.2 .readMask).outputs .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then maskOfNat 0 else updated .mem_wstrb := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .readMask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [readValue, updatedFieldsValue, zeroMaskValue] at equation
    exact equation
  have readPhaseValue : (proposal.2 .readPhase).outputs .result =
      bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
          memoryInputs.mem_do_rdata then stateOfNat 1 else updated .mem_state := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .readPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [readValue, updatedFieldsValue, readStateValue] at equation
    exact equation
  have finalValidValue : (proposal.2 .finalValid).outputs .result =
      bif memoryInputs.mem_do_wdata then true else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata then true else updated .mem_valid := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .finalValid).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fieldValue .mem_do_wdata, readValidValue, trueValue] at equation
    exact equation
  have finalInstrValue : (proposal.2 .finalInstr).outputs .result =
      bif memoryInputs.mem_do_wdata then false else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata
          then memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst
          else updated .mem_instr := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .finalInstr).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fieldValue .mem_do_wdata, readInstrValue, falseValue] at equation
    exact equation
  have finalPhaseValue : (proposal.2 .finalPhase).outputs .result =
      bif memoryInputs.mem_do_wdata then stateOfNat 2 else
        bif memoryInputs.mem_do_prefetch || memoryInputs.mem_do_rinst ||
            memoryInputs.mem_do_rdata then stateOfNat 1 else updated .mem_state := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .finalPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fieldValue .mem_do_wdata, readPhaseValue, writeStateValue] at equation
    exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralResult memoryInputs updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralResult]
    · exact finalPhaseValue
    · exact finalValidValue
    · exact finalInstrValue
    · simpa using congrFun updatedFieldsValue .mem_addr
    · simpa using congrFun updatedFieldsValue .mem_wdata
    · exact readMaskValue
    · simpa using congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (structuralResult memoryInputs updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.IdleUpdate
