import Silean.Examples.PicoRV.Memory.MemoryLookaheadCapture
import Silean.Examples.PicoRV.Memory.MemoryLookaheadCertified
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Memory.LookaheadCapture

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  lookahead := Lookahead.certification,
  active := Primitives.orCertified.certification,
  zeroMask := Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0),
  writeMask := Modules.Mux.certification (.vector 4 .bit),
  address := Modules.Mux.certification (.vector 32 .bit),
  mask := Modules.Mux.certification (.vector 4 .bit),
  writeData := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Modules.NamedTupleSplitter.Rule.apply,
    .lookahead => Lookahead.Rule.memLaRead,
    .lookahead => Lookahead.Rule.memLaWrite,
    .lookahead => Lookahead.Rule.memLaAddr,
    .lookahead => Lookahead.Rule.memLaWdata,
    .lookahead => Lookahead.Rule.memLaWstrb,
    .active => Primitives.OrRule.apply,
    .zeroMask => Primitives.ConstantRule.apply,
    .writeMask => Modules.Mux.Rule.select,
    {.address, .mask, .writeData} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
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
    simp [structuralResult, lookaheadCaptured, read, write, SignalMap.set]

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
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have memoryInputsFields : MemoryInputs.signalMap.unpack (inputs .inputs) =
      memoryInputs.toValues := by
    funext field
    cases field <;> rfl
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have laReadValue : (proposal.2 .lookahead).outputs .mem_la_read =
      memLaRead memoryInputs current := by
    have equation := (Lookahead.memLaReadRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).1.1 Lookahead.Rule.memLaRead)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, Lookahead.readValue, memLaRead, memoryInputs,
      current] using equation
  have laWriteValue : (proposal.2 .lookahead).outputs .mem_la_write =
      memLaWrite memoryInputs current := by
    have equation := (Lookahead.memLaWriteRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).1.1 Lookahead.Rule.memLaWrite)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, Lookahead.writeValue, memLaWrite, memoryInputs,
      current] using equation
  have laAddrValue : (proposal.2 .lookahead).outputs .mem_la_addr =
      memLaAddr memoryInputs := by
    have equation := (Lookahead.memLaAddrRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).1.1 Lookahead.Rule.memLaAddr)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, memLaAddr, memoryInputs] using equation
  have laWdataValue : (proposal.2 .lookahead).outputs .mem_la_wdata =
      formattedWriteData memoryInputs := by
    have equation := (Lookahead.memLaWdataRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).1.1 Lookahead.Rule.memLaWdata)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, formattedWriteData, memoryInputs] using equation
  have laWstrbValue : (proposal.2 .lookahead).outputs .mem_la_wstrb =
      formattedWriteMask memoryInputs := by
    have equation := (Lookahead.memLaWstrbRule_holds_iff _ _ _).mp
      ((childMatch .lookahead).1.1 Lookahead.Rule.memLaWstrb)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputsFieldsValue, memoryInputsFields] at equation
    simpa [Inputs.toValues, formattedWriteMask, memoryInputs] using equation
  have activeValue : (proposal.2 .active).outputs .output =
      (memLaRead memoryInputs current || memLaWrite memoryInputs current) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .active).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [laReadValue, laWriteValue] at equation
    exact equation
  have zeroMaskValue := (Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0) _ _ _).mp
    ((childMatch .zeroMask).1.1 Primitives.ConstantRule.apply)
  have writeMaskValue : (proposal.2 .writeMask).outputs .result =
      bif memLaWrite memoryInputs current
        then formattedWriteMask memoryInputs else maskOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .writeMask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [laWriteValue, laWstrbValue, zeroMaskValue] at equation
    exact equation
  have addressValue : (proposal.2 .address).outputs .result =
      bif memLaRead memoryInputs current || memLaWrite memoryInputs current
        then memLaAddr memoryInputs else updated .mem_addr := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .address).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [activeValue, updatedFieldsValue, laAddrValue] at equation
    exact equation
  have maskValue : (proposal.2 .mask).outputs .result =
      bif memLaRead memoryInputs current || memLaWrite memoryInputs current then
        bif memLaWrite memoryInputs current
          then formattedWriteMask memoryInputs else maskOfNat 0
        else updated .mem_wstrb := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .mask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [activeValue, updatedFieldsValue, writeMaskValue] at equation
    exact equation
  have writeDataValue : (proposal.2 .writeData).outputs .result =
      bif memLaWrite memoryInputs current
        then formattedWriteData memoryInputs else updated .mem_wdata := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .writeData).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [laWriteValue, updatedFieldsValue, laWdataValue] at equation
    exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralResult memoryInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralResult]
    · simpa using congrFun updatedFieldsValue .mem_state
    · simpa using congrFun updatedFieldsValue .mem_valid
    · simpa using congrFun updatedFieldsValue .mem_instr
    · exact addressValue
    · exact writeDataValue
    · exact maskValue
    · simpa using congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (structuralResult memoryInputs current updated) := by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.LookaheadCapture
