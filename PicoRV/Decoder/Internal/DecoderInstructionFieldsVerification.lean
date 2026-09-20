import PicoRV.Decoder.DecoderInstructionFields
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.Constant

/-! Internal schedule and structural certification for instruction fields. -/

namespace PicoRV.Decoder.InstructionFields.Structure

open Silean
open Silean.Authoring
open InstructionMatch
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  funct3Bits := Silean.Modules.VectorLayout.certification 32 3 funct3Layout,
  funct7Bits := Silean.Modules.VectorLayout.certification 32 7 funct7Layout,
  opcodeBits := Silean.Modules.VectorLayout.certification 32 7 opcodeLayout,
  systemMiddleBits := Silean.Modules.VectorLayout.certification 32 11 systemMiddleLayout,
  systemOuterBits := Silean.Modules.VectorLayout.certification 32 13 systemOuterLayout,
  funct3Equals (code : Fin 8) := Silean.Modules.EqualsConstant.certification
    (.vector 3 .bit) (Silean.BitVector.ofNat 3 code.val),
  funct7Zero := Silean.Modules.EqualsConstant.certification
    (.vector 7 .bit) (Silean.BitVector.ofNat 7 0),
  funct7Alternate := Silean.Modules.EqualsConstant.certification
    (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x20),
  opcodeSystem := Silean.Modules.EqualsConstant.certification
    (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x73),
  opcodeFence := Silean.Modules.EqualsConstant.certification
    (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x0f),
  systemMiddleZero := Silean.Modules.EqualsConstant.certification
    (.vector 11 .bit) (Silean.BitVector.ofNat 11 0),
  systemOuterZero := Silean.Modules.EqualsConstant.certification
    (.vector 13 .bit) (Silean.BitVector.ofNat 13 0),
  trueValue := Silean.Primitives.constantCertified true |>.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .funct3Bits => Silean.Modules.VectorLayout.Rule.apply,
    .funct7Bits => Silean.Modules.VectorLayout.Rule.apply,
    .opcodeBits => Silean.Modules.VectorLayout.Rule.apply,
    .systemMiddleBits => Silean.Modules.VectorLayout.Rule.apply,
    .systemOuterBits => Silean.Modules.VectorLayout.Rule.apply,
    .funct3Equals 0 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 1 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 2 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 3 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 4 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 5 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 6 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct3Equals 7 => Silean.Modules.EqualsConstant.Rule.apply,
    .funct7Zero => Silean.Modules.EqualsConstant.Rule.apply,
    .funct7Alternate => Silean.Modules.EqualsConstant.Rule.apply,
    .opcodeSystem => Silean.Modules.EqualsConstant.Rule.apply,
    .opcodeFence => Silean.Modules.EqualsConstant.Rule.apply,
    .systemMiddleZero => Silean.Modules.EqualsConstant.Rule.apply,
    .systemOuterZero => Silean.Modules.EqualsConstant.Rule.apply,
    .trueValue => Silean.Primitives.ConstantRule.apply]
  state := []

private theorem fieldLayout_toNat (word : Word) (low width : Nat)
    (inside : low + width ≤ 32) :
    Silean.BitVector.toNat width (fun index => word ⟨index.val + low, by omega⟩) =
      field word low width := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inField : index < width
  · rw [Silean.BitVector.testBit_toNat width _ ⟨index, inField⟩]
    simp only [field, Nat.testBit_mod_two_pow, inField, decide_true,
      Bool.true_and, Nat.testBit_div_two_pow]
    exact (Silean.BitVector.testBit_toNat 32 word ⟨index + low, by omega⟩).symm
  · have leftBound := Silean.BitVector.toNat_lt_cardinality width
        (fun index => word ⟨index.val + low, by omega⟩)
    have rightBound : field word low width < 2 ^ width :=
      Nat.mod_lt _ (Nat.two_pow_pos width)
    rw [Silean.BitVector.cardinality_eq_pow] at leftBound
    have powers : 2 ^ width ≤ 2 ^ index :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt inField)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le leftBound powers)]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le rightBound powers)]

private theorem vector_equal_field (word : Word) (actual : Fin width → Bool)
    (low code : Nat)
    (actualValue : Silean.BitVector.toNat width actual = field word low width)
    (codeBound : code < 2 ^ width) :
    (Silean.SignalType.vector width .bit).equal actual (Silean.BitVector.ofNat width code) =
      decide (field word low width = code) := by
  apply Bool.eq_iff_iff.mpr
  rw [Silean.SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro equal
    have values := congrArg (Silean.BitVector.toNat width) equal
    rw [actualValue, Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt codeBound] at values
    exact values
  · intro equal
    apply Silean.BitVector.toNat_injective width
    rw [actualValue, Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt codeBound, equal]

private theorem funct3Layout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply funct3Layout word =
      fun index => word ⟨index.val + 12, by omega⟩ := by
  funext index
  rfl

private theorem funct7Layout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply funct7Layout word =
      fun index => word ⟨index.val + 25, by omega⟩ := by
  funext index
  rfl

private theorem opcodeLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply opcodeLayout word =
      fun index => word ⟨index.val, by omega⟩ := by
  funext index
  rfl

private theorem systemMiddleLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply systemMiddleLayout word =
      fun index => word ⟨index.val + 21, by omega⟩ := by
  funext index
  rfl

private theorem systemOuterLayout_apply (word : Word) :
    Silean.Modules.VectorLayout.apply systemOuterLayout word =
      fun index => word ⟨index.val + 7, by omega⟩ := by
  funext index
  rfl

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements : Silean.Contracts.Cycle.ImplementsSolutions
    (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have funct3BitsValue : hierStep.childOutputs .funct3Bits .output =
      Silean.Modules.VectorLayout.apply funct3Layout (hierStep.inputs .word) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 3 funct3Layout (childMatch .funct3Bits).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have funct7BitsValue : hierStep.childOutputs .funct7Bits .output =
      Silean.Modules.VectorLayout.apply funct7Layout (hierStep.inputs .word) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 7 funct7Layout (childMatch .funct7Bits).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have opcodeBitsValue : hierStep.childOutputs .opcodeBits .output =
      Silean.Modules.VectorLayout.apply opcodeLayout (hierStep.inputs .word) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 7 opcodeLayout (childMatch .opcodeBits).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have systemMiddleBitsValue : hierStep.childOutputs .systemMiddleBits .output =
      Silean.Modules.VectorLayout.apply systemMiddleLayout (hierStep.inputs .word) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 11 systemMiddleLayout (childMatch .systemMiddleBits).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have systemOuterBitsValue : hierStep.childOutputs .systemOuterBits .output =
      Silean.Modules.VectorLayout.apply systemOuterLayout (hierStep.inputs .word) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed
      32 13 systemOuterLayout (childMatch .systemOuterBits).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have funct3Value (code : Fin 8) :
      hierStep.childOutputs (.funct3Equals code) .result =
        decide (funct3 (hierStep.inputs .word) = code.val) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 3 .bit) (Silean.BitVector.ofNat 3 code.val)
      (childMatch (.funct3Equals code)).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 3 .bit).equal actual (Silean.BitVector.ofNat 3 code.val))
      funct3BitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 12 code.val
    · rw [funct3Layout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 12 3 (by omega)
    · exact code.isLt
  have funct7ZeroValue : hierStep.childOutputs .funct7Zero .result =
      decide (funct7 (hierStep.inputs .word) = 0) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 7 .bit) (Silean.BitVector.ofNat 7 0)
      (childMatch .funct7Zero).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 7 .bit).equal actual (Silean.BitVector.ofNat 7 0))
      funct7BitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 25 0
    · rw [funct7Layout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 25 7 (by omega)
    · decide
  have funct7AlternateValue : hierStep.childOutputs .funct7Alternate .result =
      decide (funct7 (hierStep.inputs .word) = 0x20) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x20)
      (childMatch .funct7Alternate).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 7 .bit).equal actual (Silean.BitVector.ofNat 7 0x20))
      funct7BitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 25 0x20
    · rw [funct7Layout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 25 7 (by omega)
    · decide
  have opcodeSystemValue : hierStep.childOutputs .opcodeSystem .result =
      decide (opcode (hierStep.inputs .word) = 0x73) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x73)
      (childMatch .opcodeSystem).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 7 .bit).equal actual (Silean.BitVector.ofNat 7 0x73))
      opcodeBitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 0 0x73
    · rw [opcodeLayout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 0 7 (by omega)
    · decide
  have opcodeFenceValue : hierStep.childOutputs .opcodeFence .result =
      decide (opcode (hierStep.inputs .word) = 0x0f) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 7 .bit) (Silean.BitVector.ofNat 7 0x0f)
      (childMatch .opcodeFence).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 7 .bit).equal actual (Silean.BitVector.ofNat 7 0x0f))
      opcodeBitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 0 0x0f
    · rw [opcodeLayout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 0 7 (by omega)
    · decide
  have systemMiddleZeroValue : hierStep.childOutputs .systemMiddleZero .result =
      decide (field (hierStep.inputs .word) 21 11 = 0) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 11 .bit) (Silean.BitVector.ofNat 11 0)
      (childMatch .systemMiddleZero).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 11 .bit).equal actual (Silean.BitVector.ofNat 11 0))
      systemMiddleBitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 21 0
    · rw [systemMiddleLayout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 21 11 (by omega)
    · decide
  have systemOuterZeroValue : hierStep.childOutputs .systemOuterZero .result =
      decide (field (hierStep.inputs .word) 7 13 = 0) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 13 .bit) (Silean.BitVector.ofNat 13 0)
      (childMatch .systemOuterZero).allowed
    normalize_child_hyp equation unfolding wiring, context
    refine (equation.trans (congrArg (fun actual =>
      (Silean.SignalType.vector 13 .bit).equal actual (Silean.BitVector.ofNat 13 0))
      systemOuterBitsValue)).trans ?_
    apply vector_equal_field (hierStep.inputs .word) _ 7 0
    · rw [systemOuterLayout_apply]
      exact fieldLayout_toNat (hierStep.inputs .word) 7 13 (by omega)
    · decide
  have trueValue : hierStep.childOutputs .trueValue .output = true := by
    exact (Silean.Primitives.constantOutputRule_holds_iff true _ _ _).mp
      ((childMatch .trueValue).ruleHolds Silean.Primitives.ConstantRule.apply)

  have boundary := satisfies.1
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    funext output
    cases output with
    | funct3_0 =>
      exact (boundary _).trans (funct3Value 0)
    | funct3_1 =>
      exact (boundary _).trans (funct3Value 1)
    | funct3_2 =>
      exact (boundary _).trans (funct3Value 2)
    | funct3_3 =>
      exact (boundary _).trans (funct3Value 3)
    | funct3_4 =>
      exact (boundary _).trans (funct3Value 4)
    | funct3_5 =>
      exact (boundary _).trans (funct3Value 5)
    | funct3_6 =>
      exact (boundary _).trans (funct3Value 6)
    | funct3_7 =>
      exact (boundary _).trans (funct3Value 7)
    | funct7_zero =>
      exact (boundary _).trans funct7ZeroValue
    | funct7_alternate =>
      exact (boundary _).trans funct7AlternateValue
    | opcode_system =>
      exact (boundary _).trans opcodeSystemValue
    | opcode_fence =>
      exact (boundary _).trans opcodeFenceValue
    | system_middle_zero =>
      exact (boundary _).trans systemMiddleZeroValue
    | system_outer_zero =>
      exact (boundary _).trans systemOuterZeroValue
    | true_value =>
      exact (boundary _).trans trueValue
  · exact Subsingleton.elim _ _

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

end PicoRV.Decoder.InstructionFields.Structure
