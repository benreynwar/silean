import PicoRV.Memory.MemoryLookahead
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BinaryToOneHot.BinaryToOneHotTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Modules.VectorSlice.VectorSliceTheorems
import Silean.Primitives.And
import Silean.Primitives.Or

namespace PicoRV.Memory.Lookahead

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  idle := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 0),
  enabledIdle := Silean.Primitives.andCertified.certification,
  instructionCommand := Silean.Primitives.orCertified.certification,
  readCommand := Silean.Primitives.orCertified.certification,
  read := Silean.Primitives.andCertified.certification,
  write := Silean.Primitives.andCertified.certification,
  alignedNextPc := Silean.Modules.VectorLayout.certification 32 32 alignedLayout,
  alignedRegOp1 := Silean.Modules.VectorLayout.certification 32 32 alignedLayout,
  address := Silean.Modules.Mux.certification (.vector 32 .bit),
  halfData := Silean.Modules.VectorLayout.certification 32 32 halfDataLayout,
  byteData := Silean.Modules.VectorLayout.certification 32 32 byteDataLayout,
  halfWordsize := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 1),
  byteWordsize := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 2),
  selectHalfData := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectByteData := Silean.Modules.Mux.certification (.vector 32 .bit),
  lowAddress := Silean.Modules.VectorSlice.certification .bit 0 2 30,
  highHalfBit := Silean.Modules.VectorSlice.certification .bit 1 1 30,
  highHalf := Silean.Modules.EqualsConstant.certification (.vector 1 .bit) (fun _ => true),
  lowHalfMask := Silean.Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0x3),
  highHalfMask := Silean.Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0xc),
  halfMask := Silean.Modules.Mux.certification (.vector 4 .bit),
  byteMask := Silean.Modules.BinaryToOneHot.certification 2,
  wordMask := Silean.Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0xf),
  selectHalfMask := Silean.Modules.Mux.certification (.vector 4 .bit),
  selectByteMask := Silean.Modules.Mux.certification (.vector 4 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .memLaRead => [
        .currentFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .idle => Silean.Modules.EqualsConstant.Rule.apply,
        .enabledIdle => Silean.Primitives.AndRule.apply,
        .instructionCommand => Silean.Primitives.OrRule.apply,
        .readCommand => Silean.Primitives.OrRule.apply,
        .read => Silean.Primitives.AndRule.apply]
    | .memLaWrite => [
        .currentFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .idle => Silean.Modules.EqualsConstant.Rule.apply,
        .enabledIdle => Silean.Primitives.AndRule.apply,
        .write => Silean.Primitives.AndRule.apply]
    | .memLaAddr => [
        .instructionCommand => Silean.Primitives.OrRule.apply,
        {.alignedNextPc, .alignedRegOp1} => Silean.Modules.VectorLayout.Rule.apply,
        .address => Silean.Modules.Mux.Rule.select]
    | .memLaWdata => [
        {.halfData, .byteData} => Silean.Modules.VectorLayout.Rule.apply,
        {.halfWordsize, .byteWordsize} => Silean.Modules.EqualsConstant.Rule.apply,
        .selectHalfData => Silean.Modules.Mux.Rule.select,
        .selectByteData => Silean.Modules.Mux.Rule.select]
    | .memLaWstrb => [
        {.halfWordsize, .byteWordsize} => Silean.Modules.EqualsConstant.Rule.apply,
        {.lowAddress, .highHalfBit} => Silean.Modules.VectorSlice.Rule.apply,
        .highHalf => Silean.Modules.EqualsConstant.Rule.apply,
        {.lowHalfMask, .highHalfMask, .wordMask} => Silean.Primitives.ConstantRule.apply,
        .halfMask => Silean.Modules.Mux.Rule.select,
        .byteMask => Silean.Modules.BinaryToOneHot.Rule.apply,
        .selectHalfMask => Silean.Modules.Mux.Rule.select,
        .selectByteMask => Silean.Modules.Mux.Rule.select]
  state := []

theorem alignedLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply alignedLayout word = aligned word := by
  funext index
  by_cases low : index.val < 2 <;>
    simp [Silean.Modules.VectorLayout.apply, alignedLayout, aligned, low]

theorem halfDataLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply halfDataLayout word =
      formattedWriteDataFrom (stateOfNat 1) word := by
  funext index
  simp [Silean.Modules.VectorLayout.apply, halfDataLayout, formattedWriteDataFrom]

theorem byteDataLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply byteDataLayout word =
      formattedWriteDataFrom (stateOfNat 2) word := by
  funext index
  simp [Silean.Modules.VectorLayout.apply, byteDataLayout, formattedWriteDataFrom]

theorem lowAddress_slice (word : Word) :
    Silean.Modules.VectorSlice.slice (α := Bool) (prefixWidth := 0)
      (width := 2) (suffixWidth := 30) word = lowAddressBits word := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem highHalf_slice (word : Word) :
    Silean.Modules.VectorSlice.slice (α := Bool) (prefixWidth := 1)
      (width := 1) (suffixWidth := 30) word = fun _ => word 1 := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem equal_single_true (bit : Bool) :
    (Silean.SignalType.vector 1 .bit).equal (fun _ => bit) (fun _ => true) = bit := by
  cases bit <;> decide

def structuralWriteData (wordsize : TwoBits) (word : Word) : Word :=
  bif decide (Silean.BitVector.toNat 2 wordsize = 2) then
    Silean.Modules.VectorLayout.apply byteDataLayout word
  else bif decide (Silean.BitVector.toNat 2 wordsize = 1) then
    Silean.Modules.VectorLayout.apply halfDataLayout word
  else word

theorem structuralWriteData_eq (wordsize : TwoBits) (word : Word) :
    structuralWriteData wordsize word = formattedWriteDataFrom wordsize word := by
  have bound := Silean.BitVector.toNat_lt_cardinality 2 wordsize
  have cases : Silean.BitVector.toNat 2 wordsize = 0 ∨
      Silean.BitVector.toNat 2 wordsize = 1 ∨
      Silean.BitVector.toNat 2 wordsize = 2 ∨
      Silean.BitVector.toNat 2 wordsize = 3 := by
    have boundFour : Silean.BitVector.toNat 2 wordsize < 4 := by
      simpa [Silean.BitVector.cardinality] using bound
    omega
  rcases cases with zero | one | two | three
  · simp [structuralWriteData, formattedWriteDataFrom, zero]
  · simpa [structuralWriteData, formattedWriteDataFrom, one] using
      halfDataLayout_apply word
  · simpa [structuralWriteData, formattedWriteDataFrom, two] using
      byteDataLayout_apply word
  · simp [structuralWriteData, formattedWriteDataFrom, three]

def structuralWriteMask (wordsize : TwoBits) (regOp1 : Word) : ByteMask :=
  bif decide (Silean.BitVector.toNat 2 wordsize = 2) then
    Silean.Modules.BinaryToOneHot.oneHot 2 (lowAddressBits regOp1)
  else bif decide (Silean.BitVector.toNat 2 wordsize = 1) then
    bif regOp1 1 then maskOfNat 0xc else maskOfNat 0x3
  else maskOfNat 0xf

theorem structuralWriteMask_eq (wordsize : TwoBits) (regOp1 : Word) :
    structuralWriteMask wordsize regOp1 = formattedWriteMaskFrom wordsize regOp1 := by
  have bound := Silean.BitVector.toNat_lt_cardinality 2 wordsize
  have cases : Silean.BitVector.toNat 2 wordsize = 0 ∨
      Silean.BitVector.toNat 2 wordsize = 1 ∨
      Silean.BitVector.toNat 2 wordsize = 2 ∨
      Silean.BitVector.toNat 2 wordsize = 3 := by
    have boundFour : Silean.BitVector.toNat 2 wordsize < 4 := by
      simpa [Silean.BitVector.cardinality] using bound
    omega
  rcases cases with zero | one | two | three
  · simp [structuralWriteMask, formattedWriteMaskFrom, zero]
  · cases high : regOp1 1 <;>
      simp [structuralWriteMask, formattedWriteMaskFrom, one, high]
  · simp [structuralWriteMask, formattedWriteMaskFrom, two]
    funext index
    rfl
  · simp [structuralWriteMask, formattedWriteMaskFrom, three]

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
  have idleValue : hierStep.childOutputs .idle .result =
      decide (stateNumber current = 0) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
      ((childMatch .idle).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, Memory.ProofSupport.equal_stateOfNat _ _ (by decide)]
      at equation
    exact equation
  have enabledValue : hierStep.childOutputs .enabledIdle .output =
      (inputs .resetn && decide (stateNumber current = 0)) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .enabledIdle).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [idleValue] at equation
    exact equation
  have instructionValue : hierStep.childOutputs .instructionCommand .output =
      (inputs .mem_do_prefetch || inputs .mem_do_rinst) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have readCommandValue : hierStep.childOutputs .readCommand .output =
      (inputs .mem_do_prefetch || inputs .mem_do_rinst ||
        inputs .mem_do_rdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .readCommand).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [instructionValue] at equation
    exact equation
  have readOutputValue : hierStep.childOutputs .read .output =
      memLaReadFrom (inputs .resetn) (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata) current := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .read).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [enabledValue, readCommandValue] at equation
    unfold memLaReadFrom
    cases resetn : inputs .resetn <;>
      cases idle : decide (stateNumber current = 0) <;>
      cases prefetch : inputs .mem_do_prefetch <;>
      cases rinst : inputs .mem_do_rinst <;>
      cases rdata : inputs .mem_do_rdata <;> simp_all
  have writeOutputValue : hierStep.childOutputs .write .output =
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) current := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .write).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [enabledValue] at equation
    change hierStep.childOutputs .write .output =
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) current at equation
    exact equation

  have alignedNextValue : hierStep.childOutputs .alignedNextPc .output =
      aligned (inputs .next_pc) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 alignedLayout (childMatch .alignedNextPc).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [alignedLayout_apply] at equation
    exact equation
  have alignedOp1Value : hierStep.childOutputs .alignedRegOp1 .output =
      aligned (inputs .reg_op1) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 alignedLayout (childMatch .alignedRegOp1).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [alignedLayout_apply] at equation
    exact equation
  have addressValue : hierStep.childOutputs .address .result =
      memLaAddrFrom (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .next_pc) (inputs .reg_op1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .address).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [instructionValue, alignedNextValue, alignedOp1Value] at equation
    cases prefetch : inputs .mem_do_prefetch <;>
      cases rinst : inputs .mem_do_rinst <;>
      simp [memLaAddrFrom, prefetch, rinst] at equation ⊢ <;>
      exact equation

  have halfDataValue : hierStep.childOutputs .halfData .output =
      Silean.Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 halfDataLayout (childMatch .halfData).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have byteDataValue : hierStep.childOutputs .byteData .output =
      Silean.Modules.VectorLayout.apply byteDataLayout (inputs .reg_op2) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 byteDataLayout (childMatch .byteData).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have halfWordsizeValue : hierStep.childOutputs .halfWordsize .result =
      decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 1) _ _ _).mp
      ((childMatch .halfWordsize).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [Memory.ProofSupport.equal_stateOfNat _ _ (by decide)] at equation
    exact equation
  have byteWordsizeValue : hierStep.childOutputs .byteWordsize .result =
      decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 2) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 2) _ _ _).mp
      ((childMatch .byteWordsize).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [Memory.ProofSupport.equal_stateOfNat _ _ (by decide)] at equation
    exact equation
  have selectHalfDataValue : hierStep.childOutputs .selectHalfData .result =
      bif Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1 then
        Silean.Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2)
        else inputs .reg_op2 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectHalfData).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [halfWordsizeValue, halfDataValue] at equation
    exact equation
  have selectByteDataValue : hierStep.childOutputs .selectByteData .result =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectByteData).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [byteWordsizeValue, byteDataValue, selectHalfDataValue] at equation
    change hierStep.childOutputs .selectByteData .result =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2)
    rw [← structuralWriteData_eq]
    change hierStep.childOutputs .selectByteData .result =
      bif decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 2) then
        Silean.Modules.VectorLayout.apply byteDataLayout (inputs .reg_op2)
      else bif decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1) then
        Silean.Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2)
      else inputs .reg_op2
    exact equation

  have lowAddressValue : hierStep.childOutputs .lowAddress .result =
      lowAddressBits (inputs .reg_op1) := by
    have equation := Silean.Modules.VectorSlice.result_of_allowed
      .bit 0 2 30 (childMatch .lowAddress).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (lowAddress_slice (inputs .reg_op1))
  have highHalfBitValue : hierStep.childOutputs .highHalfBit .result =
      (fun _ => inputs .reg_op1 1) := by
    have equation := Silean.Modules.VectorSlice.result_of_allowed
      .bit 1 1 30 (childMatch .highHalfBit).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (highHalf_slice (inputs .reg_op1))
  have highHalfValue : hierStep.childOutputs .highHalf .result =
      inputs .reg_op1 1 := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 1 .bit) (fun _ => true) _ _ _).mp
      ((childMatch .highHalf).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [highHalfBitValue, equal_single_true] at equation
    exact equation
  have lowHalfMaskValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0x3) _ _ _).mp
    ((childMatch .lowHalfMask).ruleHolds Silean.Primitives.ConstantRule.apply)
  have highHalfMaskValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0xc) _ _ _).mp
    ((childMatch .highHalfMask).ruleHolds Silean.Primitives.ConstantRule.apply)
  have wordMaskValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0xf) _ _ _).mp
    ((childMatch .wordMask).ruleHolds Silean.Primitives.ConstantRule.apply)
  have halfMaskValue : hierStep.childOutputs .halfMask .result =
      bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .halfMask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [highHalfValue, lowHalfMaskValue, highHalfMaskValue] at equation
    exact equation
  have byteMaskValue : hierStep.childOutputs .byteMask .result =
      Silean.Modules.BinaryToOneHot.oneHot 2 (lowAddressBits (inputs .reg_op1)) := by
    have equation := (Silean.Modules.BinaryToOneHot.outputRule_holds_iff 2 _ _ _).mp
      ((childMatch .byteMask).ruleHolds Silean.Modules.BinaryToOneHot.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [lowAddressValue] at equation
    exact equation
  have selectHalfMaskValue : hierStep.childOutputs .selectHalfMask .result =
      bif Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1 then
        (bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3)
        else maskOfNat 0xf := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .selectHalfMask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [halfWordsizeValue, halfMaskValue, wordMaskValue] at equation
    exact equation
  have selectByteMaskValue : hierStep.childOutputs .selectByteMask .result =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 4 .bit)
      (childMatch .selectByteMask).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [byteWordsizeValue, byteMaskValue, selectHalfMaskValue] at equation
    change hierStep.childOutputs .selectByteMask .result =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1)
    rw [← structuralWriteMask_eq]
    change hierStep.childOutputs .selectByteMask .result =
      bif decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 2) then
        Silean.Modules.BinaryToOneHot.oneHot 2 (lowAddressBits (inputs .reg_op1))
      else bif decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1) then
        bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3
      else maskOfNat 0xf
    exact equation

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    dsimp only
    cases rule
    · rw [memLaReadRule_holds_iff]
      rw [show hierStep.outputs .mem_la_read =
          hierStep.childOutputs .read .output by exact satisfies.1 .mem_la_read]
      simpa [Lookahead.readValue, current] using readOutputValue
    · rw [memLaWriteRule_holds_iff]
      rw [show hierStep.outputs .mem_la_write =
          hierStep.childOutputs .write .output by exact satisfies.1 .mem_la_write]
      simpa [Lookahead.writeValue, current] using writeOutputValue
    · rw [memLaAddrRule_holds_iff]
      rw [show hierStep.outputs .mem_la_addr =
          hierStep.childOutputs .address .result by exact satisfies.1 .mem_la_addr]
      exact addressValue
    · rw [memLaWdataRule_holds_iff]
      rw [show hierStep.outputs .mem_la_wdata =
          hierStep.childOutputs .selectByteData .result by
            exact satisfies.1 .mem_la_wdata]
      exact selectByteDataValue
    · rw [memLaWstrbRule_holds_iff]
      rw [show hierStep.outputs .mem_la_wstrb =
          hierStep.childOutputs .selectByteMask .result by
            exact satisfies.1 .mem_la_wstrb]
      exact selectByteMaskValue
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

end PicoRV.Memory.Lookahead
