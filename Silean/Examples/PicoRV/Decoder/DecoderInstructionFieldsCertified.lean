import Silean.Examples.PicoRV.Decoder.DecoderInstructionFields
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.Constant

namespace Silean.Examples.PicoRV.Decoder.InstructionFields.Structure

open Silean
open Silean.Authoring
open InstructionMatch
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  funct3Bits := Modules.VectorLayout.certification 32 3 funct3Layout,
  funct7Bits := Modules.VectorLayout.certification 32 7 funct7Layout,
  opcodeBits := Modules.VectorLayout.certification 32 7 opcodeLayout,
  systemMiddleBits := Modules.VectorLayout.certification 32 11 systemMiddleLayout,
  systemOuterBits := Modules.VectorLayout.certification 32 13 systemOuterLayout,
  funct3Equals (code : Fin 8) := Modules.EqualsConstant.certification
    (.vector 3 .bit) (BitVector.ofNat 3 code.val),
  funct7Zero := Modules.EqualsConstant.certification
    (.vector 7 .bit) (BitVector.ofNat 7 0),
  funct7Alternate := Modules.EqualsConstant.certification
    (.vector 7 .bit) (BitVector.ofNat 7 0x20),
  opcodeSystem := Modules.EqualsConstant.certification
    (.vector 7 .bit) (BitVector.ofNat 7 0x73),
  opcodeFence := Modules.EqualsConstant.certification
    (.vector 7 .bit) (BitVector.ofNat 7 0x0f),
  systemMiddleZero := Modules.EqualsConstant.certification
    (.vector 11 .bit) (BitVector.ofNat 11 0),
  systemOuterZero := Modules.EqualsConstant.certification
    (.vector 13 .bit) (BitVector.ofNat 13 0),
  trueValue := Primitives.constantCertified true |>.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .funct3Bits => Modules.VectorLayout.Rule.apply,
    .funct7Bits => Modules.VectorLayout.Rule.apply,
    .opcodeBits => Modules.VectorLayout.Rule.apply,
    .systemMiddleBits => Modules.VectorLayout.Rule.apply,
    .systemOuterBits => Modules.VectorLayout.Rule.apply,
    .funct3Equals 0 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 1 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 2 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 3 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 4 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 5 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 6 => Modules.EqualsConstant.Rule.apply,
    .funct3Equals 7 => Modules.EqualsConstant.Rule.apply,
    .funct7Zero => Modules.EqualsConstant.Rule.apply,
    .funct7Alternate => Modules.EqualsConstant.Rule.apply,
    .opcodeSystem => Modules.EqualsConstant.Rule.apply,
    .opcodeFence => Modules.EqualsConstant.Rule.apply,
    .systemMiddleZero => Modules.EqualsConstant.Rule.apply,
    .systemOuterZero => Modules.EqualsConstant.Rule.apply,
    .trueValue => Primitives.ConstantRule.apply]
  state := []

private theorem fieldLayout_toNat (word : Word) (low width : Nat)
    (inside : low + width ≤ 32) :
    BitVector.toNat width (fun index => word ⟨index.val + low, by omega⟩) =
      field word low width := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inField : index < width
  · rw [BitVector.testBit_toNat width _ ⟨index, inField⟩]
    simp only [field, Nat.testBit_mod_two_pow, inField, decide_true,
      Bool.true_and, Nat.testBit_div_two_pow]
    exact (BitVector.testBit_toNat 32 word ⟨index + low, by omega⟩).symm
  · have leftBound := BitVector.toNat_lt_cardinality width
        (fun index => word ⟨index.val + low, by omega⟩)
    have rightBound : field word low width < 2 ^ width :=
      Nat.mod_lt _ (Nat.two_pow_pos width)
    rw [BitVector.cardinality_eq_pow] at leftBound
    have powers : 2 ^ width ≤ 2 ^ index :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt inField)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le leftBound powers)]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le rightBound powers)]

private theorem vector_equal_field (word : Word) (actual : Fin width → Bool)
    (low code : Nat)
    (actualValue : BitVector.toNat width actual = field word low width)
    (codeBound : code < 2 ^ width) :
    (SignalType.vector width .bit).equal actual (BitVector.ofNat width code) =
      decide (field word low width = code) := by
  apply Bool.eq_iff_iff.mpr
  rw [SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro equal
    have values := congrArg (BitVector.toNat width) equal
    rw [actualValue, BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt codeBound] at values
    exact values
  · intro equal
    apply BitVector.toNat_injective width
    rw [actualValue, BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt codeBound, equal]

private theorem funct3Layout_apply (word : Word) :
    Modules.VectorLayout.apply funct3Layout word =
      fun index => word ⟨index.val + 12, by omega⟩ := by
  funext index
  rfl

private theorem funct7Layout_apply (word : Word) :
    Modules.VectorLayout.apply funct7Layout word =
      fun index => word ⟨index.val + 25, by omega⟩ := by
  funext index
  rfl

private theorem opcodeLayout_apply (word : Word) :
    Modules.VectorLayout.apply opcodeLayout word =
      fun index => word ⟨index.val, by omega⟩ := by
  funext index
  rfl

private theorem systemMiddleLayout_apply (word : Word) :
    Modules.VectorLayout.apply systemMiddleLayout word =
      fun index => word ⟨index.val + 21, by omega⟩ := by
  funext index
  rfl

private theorem systemOuterLayout_apply (word : Word) :
    Modules.VectorLayout.apply systemOuterLayout word =
      fun index => word ⟨index.val + 7, by omega⟩ := by
  funext index
  rfl

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  have funct3BitsValue : (proposal.2 .funct3Bits).outputs .output =
      Modules.VectorLayout.apply funct3Layout (inputs .word) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 3 funct3Layout _ _ _ _ (childMatch .funct3Bits).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have funct7BitsValue : (proposal.2 .funct7Bits).outputs .output =
      Modules.VectorLayout.apply funct7Layout (inputs .word) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 7 funct7Layout _ _ _ _ (childMatch .funct7Bits).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have opcodeBitsValue : (proposal.2 .opcodeBits).outputs .output =
      Modules.VectorLayout.apply opcodeLayout (inputs .word) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 7 opcodeLayout _ _ _ _ (childMatch .opcodeBits).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have systemMiddleBitsValue : (proposal.2 .systemMiddleBits).outputs .output =
      Modules.VectorLayout.apply systemMiddleLayout (inputs .word) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 11 systemMiddleLayout _ _ _ _ (childMatch .systemMiddleBits).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have systemOuterBitsValue : (proposal.2 .systemOuterBits).outputs .output =
      Modules.VectorLayout.apply systemOuterLayout (inputs .word) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo
      32 13 systemOuterLayout _ _ _ _ (childMatch .systemOuterBits).1
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation

  have funct3Value (code : Fin 8) :
      (proposal.2 (.funct3Equals code)).outputs .result =
        decide (funct3 (inputs .word) = code.val) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 3 .bit) (BitVector.ofNat 3 code.val) _ _ _).mp
      ((childMatch (.funct3Equals code)).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [funct3BitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 12 code.val
    · rw [funct3Layout_apply]
      exact fieldLayout_toNat (inputs .word) 12 3 (by omega)
    · exact code.isLt
  have funct7ZeroValue : (proposal.2 .funct7Zero).outputs .result =
      decide (funct7 (inputs .word) = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (BitVector.ofNat 7 0) _ _ _).mp
      ((childMatch .funct7Zero).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [funct7BitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 25 0
    · rw [funct7Layout_apply]
      exact fieldLayout_toNat (inputs .word) 25 7 (by omega)
    · decide
  have funct7AlternateValue : (proposal.2 .funct7Alternate).outputs .result =
      decide (funct7 (inputs .word) = 0x20) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (BitVector.ofNat 7 0x20) _ _ _).mp
      ((childMatch .funct7Alternate).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [funct7BitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 25 0x20
    · rw [funct7Layout_apply]
      exact fieldLayout_toNat (inputs .word) 25 7 (by omega)
    · decide
  have opcodeSystemValue : (proposal.2 .opcodeSystem).outputs .result =
      decide (opcode (inputs .word) = 0x73) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (BitVector.ofNat 7 0x73) _ _ _).mp
      ((childMatch .opcodeSystem).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [opcodeBitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 0 0x73
    · rw [opcodeLayout_apply]
      exact fieldLayout_toNat (inputs .word) 0 7 (by omega)
    · decide
  have opcodeFenceValue : (proposal.2 .opcodeFence).outputs .result =
      decide (opcode (inputs .word) = 0x0f) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (BitVector.ofNat 7 0x0f) _ _ _).mp
      ((childMatch .opcodeFence).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [opcodeBitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 0 0x0f
    · rw [opcodeLayout_apply]
      exact fieldLayout_toNat (inputs .word) 0 7 (by omega)
    · decide
  have systemMiddleZeroValue : (proposal.2 .systemMiddleZero).outputs .result =
      decide (field (inputs .word) 21 11 = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 11 .bit) (BitVector.ofNat 11 0) _ _ _).mp
      ((childMatch .systemMiddleZero).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [systemMiddleBitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 21 0
    · rw [systemMiddleLayout_apply]
      exact fieldLayout_toNat (inputs .word) 21 11 (by omega)
    · decide
  have systemOuterZeroValue : (proposal.2 .systemOuterZero).outputs .result =
      decide (field (inputs .word) 7 13 = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 13 .bit) (BitVector.ofNat 13 0) _ _ _).mp
      ((childMatch .systemOuterZero).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [systemOuterBitsValue] at equation
    rw [equation]
    apply vector_equal_field (inputs .word) _ 7 0
    · rw [systemOuterLayout_apply]
      exact fieldLayout_toNat (inputs .word) 7 13 (by omega)
    · decide
  have trueValue : (proposal.2 .trueValue).outputs .output = true := by
    exact (Primitives.constantOutputRule_holds_iff true _ _ _).mp
      ((childMatch .trueValue).1.1 Primitives.ConstantRule.apply)

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output with
    | funct3_0 =>
      rw [show proposal.outputs .funct3_0 =
        (proposal.2 (.funct3Equals 0)).outputs .result by exact boundary _]
      exact funct3Value 0
    | funct3_1 =>
      rw [show proposal.outputs .funct3_1 =
        (proposal.2 (.funct3Equals 1)).outputs .result by exact boundary _]
      exact funct3Value 1
    | funct3_2 =>
      rw [show proposal.outputs .funct3_2 =
        (proposal.2 (.funct3Equals 2)).outputs .result by exact boundary _]
      exact funct3Value 2
    | funct3_3 =>
      rw [show proposal.outputs .funct3_3 =
        (proposal.2 (.funct3Equals 3)).outputs .result by exact boundary _]
      exact funct3Value 3
    | funct3_4 =>
      rw [show proposal.outputs .funct3_4 =
        (proposal.2 (.funct3Equals 4)).outputs .result by exact boundary _]
      exact funct3Value 4
    | funct3_5 =>
      rw [show proposal.outputs .funct3_5 =
        (proposal.2 (.funct3Equals 5)).outputs .result by exact boundary _]
      exact funct3Value 5
    | funct3_6 =>
      rw [show proposal.outputs .funct3_6 =
        (proposal.2 (.funct3Equals 6)).outputs .result by exact boundary _]
      exact funct3Value 6
    | funct3_7 =>
      rw [show proposal.outputs .funct3_7 =
        (proposal.2 (.funct3Equals 7)).outputs .result by exact boundary _]
      exact funct3Value 7
    | funct7_zero =>
      rw [show proposal.outputs .funct7_zero =
        (proposal.2 .funct7Zero).outputs .result by exact boundary _]
      exact funct7ZeroValue
    | funct7_alternate =>
      rw [show proposal.outputs .funct7_alternate =
        (proposal.2 .funct7Alternate).outputs .result by exact boundary _]
      exact funct7AlternateValue
    | opcode_system =>
      rw [show proposal.outputs .opcode_system =
        (proposal.2 .opcodeSystem).outputs .result by exact boundary _]
      exact opcodeSystemValue
    | opcode_fence =>
      rw [show proposal.outputs .opcode_fence =
        (proposal.2 .opcodeFence).outputs .result by exact boundary _]
      exact opcodeFenceValue
    | system_middle_zero =>
      rw [show proposal.outputs .system_middle_zero =
        (proposal.2 .systemMiddleZero).outputs .result by exact boundary _]
      exact systemMiddleZeroValue
    | system_outer_zero =>
      rw [show proposal.outputs .system_outer_zero =
        (proposal.2 .systemOuterZero).outputs .result by exact boundary _]
      exact systemOuterZeroValue
    | true_value =>
      rw [show proposal.outputs .true_value =
        (proposal.2 .trueValue).outputs .output by exact boundary _]
      exact trueValue
  · exact Subsingleton.elim _ _

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

end Silean.Examples.PicoRV.Decoder.InstructionFields.Structure
