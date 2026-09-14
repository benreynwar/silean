import Silean.Examples.PicoRV.Memory.MemoryLookahead
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Modules.VectorSlice.VectorSliceCertified
import Silean.Primitives.And
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Memory.Lookahead

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  idle := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 0),
  enabledIdle := Primitives.andCertified.certification,
  instructionCommand := Primitives.orCertified.certification,
  readCommand := Primitives.orCertified.certification,
  read := Primitives.andCertified.certification,
  write := Primitives.andCertified.certification,
  alignedNextPc := Modules.VectorLayout.certification 32 32 alignedLayout,
  alignedRegOp1 := Modules.VectorLayout.certification 32 32 alignedLayout,
  address := Modules.Mux.certification (.vector 32 .bit),
  halfData := Modules.VectorLayout.certification 32 32 halfDataLayout,
  byteData := Modules.VectorLayout.certification 32 32 byteDataLayout,
  halfWordsize := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 1),
  byteWordsize := Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 2),
  selectHalfData := Modules.Mux.certification (.vector 32 .bit),
  selectByteData := Modules.Mux.certification (.vector 32 .bit),
  lowAddress := Modules.VectorSlice.certification .bit 0 2 30,
  highHalfBit := Modules.VectorSlice.certification .bit 1 1 30,
  highHalf := Modules.EqualsConstant.certification (.vector 1 .bit) (fun _ => true),
  lowHalfMask := Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0x3),
  highHalfMask := Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0xc),
  halfMask := Modules.Mux.certification (.vector 4 .bit),
  byteMask := Modules.BinaryToOneHot.certification 2,
  wordMask := Modules.Constant.certification (.vector 4 .bit) (maskOfNat 0xf),
  selectHalfMask := Modules.Mux.certification (.vector 4 .bit),
  selectByteMask := Modules.Mux.certification (.vector 4 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .memLaRead => [
        .currentFields => Modules.NamedTupleSplitter.Rule.apply,
        .idle => Modules.EqualsConstant.Rule.apply,
        .enabledIdle => Primitives.AndRule.apply,
        .instructionCommand => Primitives.OrRule.apply,
        .readCommand => Primitives.OrRule.apply,
        .read => Primitives.AndRule.apply]
    | .memLaWrite => [
        .currentFields => Modules.NamedTupleSplitter.Rule.apply,
        .idle => Modules.EqualsConstant.Rule.apply,
        .enabledIdle => Primitives.AndRule.apply,
        .write => Primitives.AndRule.apply]
    | .memLaAddr => [
        .instructionCommand => Primitives.OrRule.apply,
        {.alignedNextPc, .alignedRegOp1} => Modules.VectorLayout.Rule.apply,
        .address => Modules.Mux.Rule.select]
    | .memLaWdata => [
        {.halfData, .byteData} => Modules.VectorLayout.Rule.apply,
        {.halfWordsize, .byteWordsize} => Modules.EqualsConstant.Rule.apply,
        .selectHalfData => Modules.Mux.Rule.select,
        .selectByteData => Modules.Mux.Rule.select]
    | .memLaWstrb => [
        {.halfWordsize, .byteWordsize} => Modules.EqualsConstant.Rule.apply,
        {.lowAddress, .highHalfBit} => Modules.VectorSlice.Rule.apply,
        .highHalf => Modules.EqualsConstant.Rule.apply,
        {.lowHalfMask, .highHalfMask, .wordMask} => Primitives.ConstantRule.apply,
        .halfMask => Modules.Mux.Rule.select,
        .byteMask => Modules.BinaryToOneHot.Rule.apply,
        .selectHalfMask => Modules.Mux.Rule.select,
        .selectByteMask => Modules.Mux.Rule.select]
  state := []

theorem alignedLayout_apply (word : Word) :
    Modules.VectorLayout.apply alignedLayout word = aligned word := by
  funext index
  by_cases low : index.val < 2 <;>
    simp [Modules.VectorLayout.apply, alignedLayout, aligned, low]

theorem halfDataLayout_apply (word : Word) :
    Modules.VectorLayout.apply halfDataLayout word =
      formattedWriteDataFrom (stateOfNat 1) word := by
  funext index
  simp [Modules.VectorLayout.apply, halfDataLayout, formattedWriteDataFrom]

theorem byteDataLayout_apply (word : Word) :
    Modules.VectorLayout.apply byteDataLayout word =
      formattedWriteDataFrom (stateOfNat 2) word := by
  funext index
  simp [Modules.VectorLayout.apply, byteDataLayout, formattedWriteDataFrom]

theorem lowAddress_slice (word : Word) :
    Modules.VectorSlice.slice (α := Bool) (prefixWidth := 0)
      (width := 2) (suffixWidth := 30) word = lowAddressBits word := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem highHalf_slice (word : Word) :
    Modules.VectorSlice.slice (α := Bool) (prefixWidth := 1)
      (width := 1) (suffixWidth := 30) word = fun _ => word 1 := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem equal_single_true (bit : Bool) :
    (SignalType.vector 1 .bit).equal (fun _ => bit) (fun _ => true) = bit := by
  cases bit <;> decide

def structuralWriteData (wordsize : TwoBits) (word : Word) : Word :=
  bif decide (BitVector.toNat 2 wordsize = 2) then
    Modules.VectorLayout.apply byteDataLayout word
  else bif decide (BitVector.toNat 2 wordsize = 1) then
    Modules.VectorLayout.apply halfDataLayout word
  else word

theorem structuralWriteData_eq (wordsize : TwoBits) (word : Word) :
    structuralWriteData wordsize word = formattedWriteDataFrom wordsize word := by
  have bound := BitVector.toNat_lt_cardinality 2 wordsize
  have cases : BitVector.toNat 2 wordsize = 0 ∨
      BitVector.toNat 2 wordsize = 1 ∨
      BitVector.toNat 2 wordsize = 2 ∨
      BitVector.toNat 2 wordsize = 3 := by
    have boundFour : BitVector.toNat 2 wordsize < 4 := by
      simpa [BitVector.cardinality] using bound
    omega
  rcases cases with zero | one | two | three
  · simp [structuralWriteData, formattedWriteDataFrom, zero]
  · simpa [structuralWriteData, formattedWriteDataFrom, one] using
      halfDataLayout_apply word
  · simpa [structuralWriteData, formattedWriteDataFrom, two] using
      byteDataLayout_apply word
  · simp [structuralWriteData, formattedWriteDataFrom, three]

def structuralWriteMask (wordsize : TwoBits) (regOp1 : Word) : ByteMask :=
  bif decide (BitVector.toNat 2 wordsize = 2) then
    Modules.BinaryToOneHot.oneHot 2 (lowAddressBits regOp1)
  else bif decide (BitVector.toNat 2 wordsize = 1) then
    bif regOp1 1 then maskOfNat 0xc else maskOfNat 0x3
  else maskOfNat 0xf

theorem structuralWriteMask_eq (wordsize : TwoBits) (regOp1 : Word) :
    structuralWriteMask wordsize regOp1 = formattedWriteMaskFrom wordsize regOp1 := by
  have bound := BitVector.toNat_lt_cardinality 2 wordsize
  have cases : BitVector.toNat 2 wordsize = 0 ∨
      BitVector.toNat 2 wordsize = 1 ∨
      BitVector.toNat 2 wordsize = 2 ∨
      BitVector.toNat 2 wordsize = 3 := by
    have boundFour : BitVector.toNat 2 wordsize < 4 := by
      simpa [BitVector.cardinality] using bound
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
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  let current := stateMap.unpack (inputs .current)
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Memory.ProofSupport.splitValue_eq_unpack, current] using equation
  have idleValue : (proposal.2 .idle).outputs .result =
      decide (stateNumber current = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
      ((childMatch .idle).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, Memory.ProofSupport.equal_stateOfNat _ _ (by decide)]
      at equation
    exact equation
  have enabledValue : (proposal.2 .enabledIdle).outputs .output =
      (inputs .resetn && decide (stateNumber current = 0)) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .enabledIdle).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [idleValue] at equation
    exact equation
  have instructionValue : (proposal.2 .instructionCommand).outputs .output =
      (inputs .mem_do_prefetch || inputs .mem_do_rinst) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionCommand).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have readCommandValue : (proposal.2 .readCommand).outputs .output =
      (inputs .mem_do_prefetch || inputs .mem_do_rinst ||
        inputs .mem_do_rdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .readCommand).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instructionValue] at equation
    exact equation
  have readOutputValue : (proposal.2 .read).outputs .output =
      memLaReadFrom (inputs .resetn) (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata) current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .read).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [enabledValue, readCommandValue] at equation
    simpa [memLaReadFrom, Bool.and_assoc, Bool.or_comm,
      Bool.or_left_comm] using equation
  have writeOutputValue : (proposal.2 .write).outputs .output =
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .write).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [enabledValue] at equation
    simpa [memLaWriteFrom, Bool.and_assoc] using equation

  have alignedNextValue : (proposal.2 .alignedNextPc).outputs .output =
      aligned (inputs .next_pc) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 32 alignedLayout _ _ _ _ (childMatch .alignedNextPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [alignedLayout_apply] at equation
    exact equation
  have alignedOp1Value : (proposal.2 .alignedRegOp1).outputs .output =
      aligned (inputs .reg_op1) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 32 alignedLayout _ _ _ _ (childMatch .alignedRegOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [alignedLayout_apply] at equation
    exact equation
  have addressValue : (proposal.2 .address).outputs .result =
      memLaAddrFrom (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .next_pc) (inputs .reg_op1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .address).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instructionValue, alignedNextValue, alignedOp1Value] at equation
    cases prefetch : inputs .mem_do_prefetch <;>
      cases rinst : inputs .mem_do_rinst <;>
      simp [memLaAddrFrom, prefetch, rinst] at equation ⊢ <;>
      exact equation

  have halfDataValue : (proposal.2 .halfData).outputs .output =
      Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 32 halfDataLayout _ _ _ _ (childMatch .halfData).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have byteDataValue : (proposal.2 .byteData).outputs .output =
      Modules.VectorLayout.apply byteDataLayout (inputs .reg_op2) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 32 byteDataLayout _ _ _ _ (childMatch .byteData).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have halfWordsizeValue : (proposal.2 .halfWordsize).outputs .result =
      decide (BitVector.toNat 2 (inputs .mem_wordsize) = 1) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 1) _ _ _).mp
      ((childMatch .halfWordsize).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [Memory.ProofSupport.equal_stateOfNat _ _ (by decide)] at equation
    exact equation
  have byteWordsizeValue : (proposal.2 .byteWordsize).outputs .result =
      decide (BitVector.toNat 2 (inputs .mem_wordsize) = 2) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (stateOfNat 2) _ _ _).mp
      ((childMatch .byteWordsize).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [Memory.ProofSupport.equal_stateOfNat _ _ (by decide)] at equation
    exact equation
  have selectHalfDataValue : (proposal.2 .selectHalfData).outputs .result =
      bif BitVector.toNat 2 (inputs .mem_wordsize) = 1 then
        Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2)
        else inputs .reg_op2 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectHalfData).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [halfWordsizeValue, halfDataValue] at equation
    exact equation
  have selectByteDataValue : (proposal.2 .selectByteData).outputs .result =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectByteData).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [byteWordsizeValue, byteDataValue, selectHalfDataValue] at equation
    change (proposal.2 .selectByteData).outputs .result =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2)
    rw [← structuralWriteData_eq]
    change (proposal.2 .selectByteData).outputs .result =
      bif decide (BitVector.toNat 2 (inputs .mem_wordsize) = 2) then
        Modules.VectorLayout.apply byteDataLayout (inputs .reg_op2)
      else bif decide (BitVector.toNat 2 (inputs .mem_wordsize) = 1) then
        Modules.VectorLayout.apply halfDataLayout (inputs .reg_op2)
      else inputs .reg_op2
    exact equation

  have lowAddressValue : (proposal.2 .lowAddress).outputs .result =
      lowAddressBits (inputs .reg_op1) := by
    have equation := Modules.VectorSlice.result_of_evaluatesTo
      .bit 0 2 30 _ _ _ _ (childMatch .lowAddress).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation.trans (lowAddress_slice (inputs .reg_op1))
  have highHalfBitValue : (proposal.2 .highHalfBit).outputs .result =
      (fun _ => inputs .reg_op1 1) := by
    have equation := Modules.VectorSlice.result_of_evaluatesTo
      .bit 1 1 30 _ _ _ _ (childMatch .highHalfBit).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation.trans (highHalf_slice (inputs .reg_op1))
  have highHalfValue : (proposal.2 .highHalf).outputs .result =
      inputs .reg_op1 1 := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 1 .bit) (fun _ => true) _ _ _).mp
      ((childMatch .highHalf).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [highHalfBitValue, equal_single_true] at equation
    exact equation
  have lowHalfMaskValue := (Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0x3) _ _ _).mp
    ((childMatch .lowHalfMask).1.1 Primitives.ConstantRule.apply)
  have highHalfMaskValue := (Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0xc) _ _ _).mp
    ((childMatch .highHalfMask).1.1 Primitives.ConstantRule.apply)
  have wordMaskValue := (Modules.Constant.outputRule_holds_iff
    (.vector 4 .bit) (maskOfNat 0xf) _ _ _).mp
    ((childMatch .wordMask).1.1 Primitives.ConstantRule.apply)
  have halfMaskValue : (proposal.2 .halfMask).outputs .result =
      bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .halfMask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [highHalfValue, lowHalfMaskValue, highHalfMaskValue] at equation
    exact equation
  have byteMaskValue : (proposal.2 .byteMask).outputs .result =
      Modules.BinaryToOneHot.oneHot 2 (lowAddressBits (inputs .reg_op1)) := by
    have equation := (Modules.BinaryToOneHot.outputRule_holds_iff 2 _ _ _).mp
      ((childMatch .byteMask).1.1 Modules.BinaryToOneHot.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [lowAddressValue] at equation
    exact equation
  have selectHalfMaskValue : (proposal.2 .selectHalfMask).outputs .result =
      bif BitVector.toNat 2 (inputs .mem_wordsize) = 1 then
        (bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3)
        else maskOfNat 0xf := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .selectHalfMask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [halfWordsizeValue, halfMaskValue, wordMaskValue] at equation
    exact equation
  have selectByteMaskValue : (proposal.2 .selectByteMask).outputs .result =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 4 .bit)
      _ _ _ _ (childMatch .selectByteMask).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [byteWordsizeValue, byteMaskValue, selectHalfMaskValue] at equation
    change (proposal.2 .selectByteMask).outputs .result =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1)
    rw [← structuralWriteMask_eq]
    change (proposal.2 .selectByteMask).outputs .result =
      bif decide (BitVector.toNat 2 (inputs .mem_wordsize) = 2) then
        Modules.BinaryToOneHot.oneHot 2 (lowAddressBits (inputs .reg_op1))
      else bif decide (BitVector.toNat 2 (inputs .mem_wordsize) = 1) then
        bif inputs .reg_op1 1 then maskOfNat 0xc else maskOfNat 0x3
      else maskOfNat 0xf
    exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    · rw [memLaReadRule_holds_iff]
      rw [show proposal.outputs .mem_la_read =
          (proposal.2 .read).outputs .output by exact satisfies.1 .mem_la_read]
      simpa [Lookahead.readValue, current] using readOutputValue
    · rw [memLaWriteRule_holds_iff]
      rw [show proposal.outputs .mem_la_write =
          (proposal.2 .write).outputs .output by exact satisfies.1 .mem_la_write]
      simpa [Lookahead.writeValue, current] using writeOutputValue
    · rw [memLaAddrRule_holds_iff]
      rw [show proposal.outputs .mem_la_addr =
          (proposal.2 .address).outputs .result by exact satisfies.1 .mem_la_addr]
      exact addressValue
    · rw [memLaWdataRule_holds_iff]
      rw [show proposal.outputs .mem_la_wdata =
          (proposal.2 .selectByteData).outputs .result by
            exact satisfies.1 .mem_la_wdata]
      exact selectByteDataValue
    · rw [memLaWstrbRule_holds_iff]
      rw [show proposal.outputs .mem_la_wstrb =
          (proposal.2 .selectByteMask).outputs .result by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.Lookahead
