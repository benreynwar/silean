import PicoRV.Memory.MemoryLookaheadCapture
import PicoRV.Memory.Internal.MemoryLookaheadVerification
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.Or

namespace PicoRV.Memory.LookaheadCapture

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  lookahead := Lookahead.certification,
  active := Silean.Primitives.orCertified.certification,
  zeroMask := Silean.Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0),
  writeMask := Silean.Modules.Mux.certification (.vector 4 .bit),
  address := Silean.Modules.Mux.certification (.vector 32 .bit),
  mask := Silean.Modules.Mux.certification (.vector 4 .bit),
  writeData := Silean.Modules.Mux.certification (.vector 32 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .lookahead => Lookahead.Rule.memLaRead,
    .lookahead => Lookahead.Rule.memLaWrite,
    .lookahead => Lookahead.Rule.memLaAddr,
    .lookahead => Lookahead.Rule.memLaWdata,
    .lookahead => Lookahead.Rule.memLaWstrb,
    .active => Silean.Primitives.OrRule.apply,
    .zeroMask => Silean.Primitives.ConstantRule.apply,
    .writeMask => Silean.Modules.Mux.Rule.select,
    {.address, .mask, .writeData} => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (memoryInputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  let laRead := memLaRead memoryInputs current
  let laWrite := memLaWrite memoryInputs current
  fun
    | .mem_addr => bif laRead || laWrite
        then memLaAddr memoryInputs else updated .mem_addr
    | .mem_wstrb => bif laRead || laWrite then
        bif laWrite then formattedWriteMask memoryInputs else maskOfNat 0
        else updated .mem_wstrb
    | .mem_wdata => bif laWrite
        then formattedWriteData memoryInputs else updated .mem_wdata
    | field => updated field

theorem structuralResult_eq_lookaheadCaptured (memoryInputs : Inputs)
    (current updated : stateMap.Values) :
    structuralResult memoryInputs current updated =
      lookaheadCaptured memoryInputs current updated := by
  cases read : memLaRead memoryInputs current <;>
    cases write : memLaWrite memoryInputs current <;>
    funext field <;> cases field <;>
    simp [structuralResult, lookaheadCaptured, read, write, Silean.SignalMap.set]

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
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have memoryInputsFields : MemoryInputs.signalMap.unpack (inputs .inputs) =
      memoryInputs.toValues := by
    funext field
    cases field <;> rfl
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have laReadValue : hierStep.childOutputs .lookahead .mem_la_read =
      memLaRead memoryInputs current := by
    have equation := (Lookahead.memLaReadRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).ruleHolds Lookahead.Rule.memLaRead)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, Lookahead.readValue, memLaRead, memoryInputs,
      current] using equation
  have laWriteValue : hierStep.childOutputs .lookahead .mem_la_write =
      memLaWrite memoryInputs current := by
    have equation := (Lookahead.memLaWriteRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).ruleHolds Lookahead.Rule.memLaWrite)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, Lookahead.writeValue, memLaWrite, memoryInputs,
      current] using equation
  have laAddrValue : hierStep.childOutputs .lookahead .mem_la_addr =
      memLaAddr memoryInputs := by
    have equation := (Lookahead.memLaAddrRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).ruleHolds Lookahead.Rule.memLaAddr)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, memLaAddr, memoryInputs] using equation
  have laWdataValue : hierStep.childOutputs .lookahead .mem_la_wdata =
      formattedWriteData memoryInputs := by
    have equation := (Lookahead.memLaWdataRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).ruleHolds Lookahead.Rule.memLaWdata)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, formattedWriteData, memoryInputs] using equation
  have laWstrbValue : hierStep.childOutputs .lookahead .mem_la_wstrb =
      formattedWriteMask memoryInputs := by
    have equation := (Lookahead.memLaWstrbRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).ruleHolds Lookahead.Rule.memLaWstrb)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, formattedWriteMask, memoryInputs] using equation
  have activeValue : hierStep.childOutputs .active .output =
      (memLaRead memoryInputs current || memLaWrite memoryInputs current) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .active).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [laReadValue, laWriteValue] at equation
    exact equation
  have zeroMaskValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0) _ _ _).mp
    ((childMatch .zeroMask).ruleHolds Silean.Primitives.ConstantRule.apply)
  have writeMaskValue : hierStep.childOutputs .writeMask .result =
      bif memLaWrite memoryInputs current
        then formattedWriteMask memoryInputs else maskOfNat 0 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .writeMask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [laWriteValue, laWstrbValue, zeroMaskValue] at equation
    exact equation
  have addressValue : hierStep.childOutputs .address .result =
      bif memLaRead memoryInputs current || memLaWrite memoryInputs current
        then memLaAddr memoryInputs else updated .mem_addr := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .address).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [activeValue, updatedFieldsValue, laAddrValue] at equation
    exact equation
  have maskValue : hierStep.childOutputs .mask .result =
      bif memLaRead memoryInputs current || memLaWrite memoryInputs current then
        bif memLaWrite memoryInputs current
          then formattedWriteMask memoryInputs else maskOfNat 0
        else updated .mem_wstrb := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .mask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [activeValue, updatedFieldsValue, writeMaskValue] at equation
    exact equation
  have writeDataValue : hierStep.childOutputs .writeData .result =
      bif memLaWrite memoryInputs current
        then formattedWriteData memoryInputs else updated .mem_wdata := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .writeData).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [laWriteValue, updatedFieldsValue, laWdataValue] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralResult memoryInputs current updated := by
    funext field
    cases field
    · change hierStep.childOutputs .updatedFields .mem_state = _
      exact congrFun updatedFieldsValue .mem_state
    · change hierStep.childOutputs .updatedFields .mem_valid = _
      exact congrFun updatedFieldsValue .mem_valid
    · change hierStep.childOutputs .updatedFields .mem_instr = _
      exact congrFun updatedFieldsValue .mem_instr
    · change hierStep.childOutputs .address .result = _; exact addressValue
    · change hierStep.childOutputs .writeData .result = _; exact writeDataValue
    · change hierStep.childOutputs .mask .result = _; exact maskValue
    · change hierStep.childOutputs .updatedFields .mem_rdata_q = _
      exact congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (structuralResult memoryInputs current updated) := by
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
    rw [resultValue, structuralResult_eq_lookaheadCaptured]
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

end PicoRV.Memory.LookaheadCapture
