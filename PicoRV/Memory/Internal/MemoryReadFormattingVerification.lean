import PicoRV.Memory.MemoryReadFormatting
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Modules.VectorSlice.VectorSliceTheorems

namespace PicoRV.Memory.ReadFormatting

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  lowBit := Silean.Modules.VectorSlice.certification .bit 0 1 31,
  highBit := Silean.Modules.VectorSlice.certification .bit 1 1 30,
  lowLane := Silean.Modules.EqualsConstant.certification (.vector 1 .bit) (fun _ => true),
  highLane := Silean.Modules.EqualsConstant.certification (.vector 1 .bit) (fun _ => true),
  halfLow := Silean.Modules.VectorLayout.certification 32 32 (halfLayout false),
  halfHigh := Silean.Modules.VectorLayout.certification 32 32 (halfLayout true),
  byte0 := Silean.Modules.VectorLayout.certification 32 32 byte0Layout,
  byte1 := Silean.Modules.VectorLayout.certification 32 32 byte1Layout,
  byte2 := Silean.Modules.VectorLayout.certification 32 32 byte2Layout,
  byte3 := Silean.Modules.VectorLayout.certification 32 32 byte3Layout,
  halfValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  lowByteValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  highByteValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  byteValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  halfWordsize := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 1),
  byteWordsize := Silean.Modules.EqualsConstant.certification (.vector 2 .bit) (stateOfNat 2),
  selectHalf := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectByte := Silean.Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.lowBit, .highBit} => Silean.Modules.VectorSlice.Rule.apply,
    {.lowLane, .highLane} => Silean.Modules.EqualsConstant.Rule.apply,
    {.halfLow, .halfHigh, .byte0, .byte1, .byte2, .byte3} =>
      Silean.Modules.VectorLayout.Rule.apply,
    {.halfValue, .lowByteValue, .highByteValue} => Silean.Modules.Mux.Rule.select,
    .byteValue => Silean.Modules.Mux.Rule.select,
    {.halfWordsize, .byteWordsize} => Silean.Modules.EqualsConstant.Rule.apply,
    .selectHalf => Silean.Modules.Mux.Rule.select,
    .selectByte => Silean.Modules.Mux.Rule.select]
  state := []

theorem halfLayout_apply (high : Bool) (word : Word) :
    Silean.Modules.VectorLayout.apply (halfLayout high) word = fun index =>
      if low : index.val < 16 then
        word ⟨index.val + if high then 16 else 0, by
          cases high <;> simp <;> omega⟩
      else false := by
  funext index
  by_cases low : index.val < 16 <;>
    simp [Silean.Modules.VectorLayout.apply, halfLayout, low]

theorem byteLayout_apply (lane : Fin 4) (word : Word) :
    Silean.Modules.VectorLayout.apply (byteLayout lane) word = fun index =>
      if low : index.val < 8 then word ⟨index.val + 8 * lane.val, by omega⟩
      else false := by
  funext index
  by_cases low : index.val < 8 <;>
    simp [Silean.Modules.VectorLayout.apply, byteLayout, low]

theorem lowBit_slice (word : Word) :
    Silean.Modules.VectorSlice.slice (α := Bool) (prefixWidth := 0)
      (width := 1) (suffixWidth := 31) word = fun _ => word 0 := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem highBit_slice (word : Word) :
    Silean.Modules.VectorSlice.slice (α := Bool) (prefixWidth := 1)
      (width := 1) (suffixWidth := 30) word = fun _ => word 1 := by
  funext index
  apply congrArg word
  apply Fin.ext
  simp

theorem equal_single_true (bit : Bool) :
    (Silean.SignalType.vector 1 .bit).equal (fun _ => bit) (fun _ => true) = bit := by
  cases bit <;> decide

def selectedHalf (regOp1 memRdata : Word) : Word :=
  bif regOp1 1 then
    Silean.Modules.VectorLayout.apply (halfLayout true) memRdata
  else
    Silean.Modules.VectorLayout.apply (halfLayout false) memRdata

def selectedByte (regOp1 memRdata : Word) : Word :=
  bif regOp1 1 then
    bif regOp1 0 then
      Silean.Modules.VectorLayout.apply byte3Layout memRdata
    else
      Silean.Modules.VectorLayout.apply byte2Layout memRdata
  else
    bif regOp1 0 then
      Silean.Modules.VectorLayout.apply byte1Layout memRdata
    else
      Silean.Modules.VectorLayout.apply byte0Layout memRdata

def structuralResult (wordsize : TwoBits) (regOp1 memRdata : Word) : Word :=
  bif decide (Silean.BitVector.toNat 2 wordsize = 2) then selectedByte regOp1 memRdata
  else bif decide (Silean.BitVector.toNat 2 wordsize = 1) then selectedHalf regOp1 memRdata
  else memRdata

theorem selectedHalf_eq (regOp1 memRdata : Word) :
    selectedHalf regOp1 memRdata =
      formattedReadDataFrom (stateOfNat 1) regOp1 memRdata := by
  cases high : regOp1 1 <;>
    simp [selectedHalf, formattedReadDataFrom, high, halfLayout_apply]

theorem selectedByte_eq (regOp1 memRdata : Word) :
    selectedByte regOp1 memRdata =
      formattedReadDataFrom (stateOfNat 2) regOp1 memRdata := by
  rw [formattedReadDataFrom, show Silean.BitVector.toNat 2 (stateOfNat 2) = 2 by decide]
  change selectedByte regOp1 memRdata = fun index =>
    if low : index.val < 8 then
      memRdata ⟨index.val + 8 * Silean.BitVector.toNat 2 (lowAddressBits regOp1), by
        have bound := Silean.BitVector.toNat_lt_cardinality 2 (lowAddressBits regOp1)
        simp [Silean.BitVector.cardinality] at bound
        omega⟩
    else false
  cases low : regOp1 0 <;> cases high : regOp1 1 <;>
    funext index
  all_goals
    simp [selectedByte, byte0Layout, byte1Layout,
      byte2Layout, byte3Layout, byteLayout_apply, lowAddressBits,
      Silean.BitVector.toNat, Silean.BitVector.cardinality, low, high]
  all_goals
    by_cases inside : index.val < 8
    · simp [inside]
      apply congrArg memRdata
      apply Fin.ext
      congr 1
    · simp [inside]

theorem structuralResult_eq (wordsize : TwoBits) (regOp1 memRdata : Word) :
    structuralResult wordsize regOp1 memRdata =
      formattedReadDataFrom wordsize regOp1 memRdata := by
  have bound := Silean.BitVector.toNat_lt_cardinality 2 wordsize
  have cases : Silean.BitVector.toNat 2 wordsize = 0 ∨
      Silean.BitVector.toNat 2 wordsize = 1 ∨
      Silean.BitVector.toNat 2 wordsize = 2 ∨
      Silean.BitVector.toNat 2 wordsize = 3 := by
    have boundFour : Silean.BitVector.toNat 2 wordsize < 4 := by
      simpa [Silean.BitVector.cardinality] using bound
    omega
  rcases cases with zero | one | two | three
  · simp [structuralResult, formattedReadDataFrom, zero]
  · have equal : wordsize = stateOfNat 1 := by
      apply Silean.BitVector.toNat_injective 2
      simpa using one
    rw [equal, structuralResult]
    simpa using selectedHalf_eq regOp1 memRdata
  · have equal : wordsize = stateOfNat 2 := by
      apply Silean.BitVector.toNat_injective 2
      simpa using two
    rw [equal, structuralResult]
    simpa using selectedByte_eq regOp1 memRdata
  · simp [structuralResult, formattedReadDataFrom, three]

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

  have lowBitValue : hierStep.childOutputs .lowBit .result =
      fun _ => inputs .reg_op1 0 := by
    have equation := Silean.Modules.VectorSlice.result_of_allowed
      .bit 0 1 31 (childMatch .lowBit).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (lowBit_slice (inputs .reg_op1))
  have highBitValue : hierStep.childOutputs .highBit .result =
      fun _ => inputs .reg_op1 1 := by
    have equation := Silean.Modules.VectorSlice.result_of_allowed
      .bit 1 1 30 (childMatch .highBit).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (highBit_slice (inputs .reg_op1))
  have lowLaneValue : hierStep.childOutputs .lowLane .result =
      inputs .reg_op1 0 := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 1 .bit) (fun _ => true) _ _ _).mp
      ((childMatch .lowLane).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [lowBitValue, equal_single_true] at equation
    exact equation
  have highLaneValue : hierStep.childOutputs .highLane .result =
      inputs .reg_op1 1 := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 1 .bit) (fun _ => true) _ _ _).mp
      ((childMatch .highLane).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [highBitValue, equal_single_true] at equation
    exact equation

  have halfLowValue : hierStep.childOutputs .halfLow .output =
      Silean.Modules.VectorLayout.apply (halfLayout false) (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 (halfLayout false) (childMatch .halfLow).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have halfHighValue : hierStep.childOutputs .halfHigh .output =
      Silean.Modules.VectorLayout.apply (halfLayout true) (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 (halfLayout true) (childMatch .halfHigh).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have byte0Value : hierStep.childOutputs .byte0 .output =
      Silean.Modules.VectorLayout.apply byte0Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 byte0Layout (childMatch .byte0).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have byte1Value : hierStep.childOutputs .byte1 .output =
      Silean.Modules.VectorLayout.apply byte1Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 byte1Layout (childMatch .byte1).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have byte2Value : hierStep.childOutputs .byte2 .output =
      Silean.Modules.VectorLayout.apply byte2Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 byte2Layout (childMatch .byte2).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have byte3Value : hierStep.childOutputs .byte3 .output =
      Silean.Modules.VectorLayout.apply byte3Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 32 byte3Layout (childMatch .byte3).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have halfValue : hierStep.childOutputs .halfValue .result =
      selectedHalf (inputs .reg_op1) (inputs .mem_rdata) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .halfValue).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [highLaneValue, halfLowValue, halfHighValue] at equation
    exact equation
  have lowByteValue : hierStep.childOutputs .lowByteValue .result =
      bif inputs .reg_op1 0 then
        Silean.Modules.VectorLayout.apply byte1Layout (inputs .mem_rdata)
      else Silean.Modules.VectorLayout.apply byte0Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .lowByteValue).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [lowLaneValue, byte0Value, byte1Value] at equation
    exact equation
  have highByteValue : hierStep.childOutputs .highByteValue .result =
      bif inputs .reg_op1 0 then
        Silean.Modules.VectorLayout.apply byte3Layout (inputs .mem_rdata)
      else Silean.Modules.VectorLayout.apply byte2Layout (inputs .mem_rdata) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .highByteValue).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [lowLaneValue, byte2Value, byte3Value] at equation
    exact equation
  have byteValue : hierStep.childOutputs .byteValue .result =
      selectedByte (inputs .reg_op1) (inputs .mem_rdata) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .byteValue).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [highLaneValue, lowByteValue, highByteValue] at equation
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
  have selectHalfValue : hierStep.childOutputs .selectHalf .result =
      bif decide (Silean.BitVector.toNat 2 (inputs .mem_wordsize) = 1) then
        selectedHalf (inputs .reg_op1) (inputs .mem_rdata)
      else inputs .mem_rdata := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectHalf).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [halfWordsizeValue, halfValue] at equation
    exact equation
  have selectByteValue : hierStep.childOutputs .selectByte .result =
      formattedReadDataFrom (inputs .mem_wordsize) (inputs .reg_op1)
        (inputs .mem_rdata) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectByte).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [byteWordsizeValue, byteValue, selectHalfValue] at equation
    rw [← structuralResult_eq]
    exact equation

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .mem_rdata_word =
        hierStep.childOutputs .selectByte .result by
      exact satisfies.1 .mem_rdata_word]
    simpa [outputValue] using selectByteValue
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

end PicoRV.Memory.ReadFormatting
