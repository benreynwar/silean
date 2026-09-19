import PicoRV.Internal.AluVerification
import PicoRV.Internal.AluCorrespondence

namespace PicoRV.Alu

open Silean

/-- The concise authored definition expands to the production hierarchy. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

/-! # PicoRV ALU theorems

This is the supported proof interface for the ALU. These statements mention
only boundary steps and source-level results; the child hierarchy, schedules,
and certification witnesses remain under `Internal/`.
-/

/-- Every contract-allowed ALU step returns the pure ALU result. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .alu_out = aluOut (valuesOf step.inputs) ∧
      step.outputs .alu_out_0 = aluOut0 (valuesOf step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-- Every realized step of the concrete hierarchy has the public ALU behavior. -/
theorem outputs_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs .alu_out = aluOut (valuesOf step.inputs) ∧
      step.outputs .alu_out_0 = aluOut0 (valuesOf step.inputs) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

/-- The authored ALU hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete ALU hierarchy have one solution for
each boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

@[simp] theorem aluOut0_eq (inputs : Values) :
    aluOut0 inputs = comparisonOutput inputs := rfl

theorem sharedUnsignedLess_whenComparing (inputs : Values)
    (comparing : inputs.is_compare = true) :
    sharedUnsignedLess inputs = unsignedLessThan inputs.reg_op1 inputs.reg_op2 := by
  unfold sharedUnsignedLess unsignedLessThan
  rw [show (inputs.instr_sub || inputs.is_compare) = true by simp [comparing]]
  rw [Silean.Modules.AddSub.addSubBits_carry_subtract]
  by_cases less : Silean.BitVector.toNat 32 inputs.reg_op1 < Silean.BitVector.toNat 32 inputs.reg_op2 <;>
    simp [less] <;> omega

theorem sharedSignedLess_whenComparing (inputs : Values)
    (comparing : inputs.is_compare = true) :
    sharedSignedLess inputs = signedLessThan inputs.reg_op1 inputs.reg_op2 := by
  unfold sharedSignedLess signedLessThan
  rw [sharedUnsignedLess_whenComparing inputs comparing]

/-- Legal arithmetic-class ADD behavior. -/
theorem aluOut_add (inputs : Values)
    (arithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = true)
    (notSubtract : inputs.instr_sub = false)
    (notCompare : inputs.is_compare = false) :
    aluOut inputs = addSub false inputs.reg_op1 inputs.reg_op2 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    arithmetic, notSubtract, notCompare]

/-- Legal arithmetic-class SUB behavior. -/
theorem aluOut_subtract (inputs : Values)
    (arithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = true)
    (subtract : inputs.instr_sub = true)
    (notCompare : inputs.is_compare = false) :
    aluOut inputs = addSub true inputs.reg_op1 inputs.reg_op2 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    arithmetic, subtract, notCompare]

/-- Legal comparison-class behavior; the selected predicate is placed in bit 0. -/
theorem aluOut_compare (inputs : Values)
    (notArithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = false)
    (compare : inputs.is_compare = true) :
    aluOut inputs = wordOfBool (comparisonOutput inputs) := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    notArithmetic, compare]

/-- Legal XOR-class behavior. -/
theorem aluOut_bitwiseXor (inputs : Values)
    (notArithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = false)
    (notCompare : inputs.is_compare = false)
    (selected : (inputs.instr_xori || inputs.instr_xor) = true) :
    aluOut inputs = bitwiseXor inputs.reg_op1 inputs.reg_op2 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    notArithmetic, notCompare, selected]

/-- Legal OR-class behavior. -/
theorem aluOut_bitwiseOr (inputs : Values)
    (notArithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = false)
    (notCompare : inputs.is_compare = false)
    (notXor : (inputs.instr_xori || inputs.instr_xor) = false)
    (selected : (inputs.instr_ori || inputs.instr_or) = true) :
    aluOut inputs = bitwiseOr inputs.reg_op1 inputs.reg_op2 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    notArithmetic, notCompare, notXor, selected]

/-- Legal AND-class behavior. -/
theorem aluOut_bitwiseAnd (inputs : Values)
    (notArithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = false)
    (notCompare : inputs.is_compare = false)
    (notXor : (inputs.instr_xori || inputs.instr_xor) = false)
    (notOr : (inputs.instr_ori || inputs.instr_or) = false)
    (selected : (inputs.instr_andi || inputs.instr_and) = true) :
    aluOut inputs = bitwiseAnd inputs.reg_op1 inputs.reg_op2 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    notArithmetic, notCompare, notXor, notOr, selected]

/-- With no result class selected, the total contract returns the zero word. -/
theorem aluOut_noSelection (inputs : Values)
    (notArithmetic : inputs.is_lui_auipc_jal_jalr_addi_add_sub = false)
    (notCompare : inputs.is_compare = false)
    (notXor : (inputs.instr_xori || inputs.instr_xor) = false)
    (notOr : (inputs.instr_ori || inputs.instr_or) = false)
    (notAnd : (inputs.instr_andi || inputs.instr_and) = false) :
    aluOut inputs = wordOfNat 0 := by
  simp [aluOut, evaluate, selectedOperation, evaluateOperation,
    notArithmetic, notCompare, notXor, notOr, notAnd]

theorem comparisonOutput_equal (inputs : Values)
    (selected : inputs.instr_beq = true) :
    comparisonOutput inputs = equal inputs.reg_op1 inputs.reg_op2 := by
  simp [comparisonOutput, selected]

theorem comparisonOutput_notEqual (inputs : Values)
    (notEqual : inputs.instr_beq = false)
    (selected : inputs.instr_bne = true) :
    comparisonOutput inputs = !(equal inputs.reg_op1 inputs.reg_op2) := by
  simp [comparisonOutput, notEqual, selected]

theorem comparisonOutput_signedGreaterOrEqual (inputs : Values)
    (notEqual : inputs.instr_beq = false) (notNotEqual : inputs.instr_bne = false)
    (selected : inputs.instr_bge = true) (comparing : inputs.is_compare = true) :
    comparisonOutput inputs = !(signedLessThan inputs.reg_op1 inputs.reg_op2) := by
  simp [comparisonOutput, notEqual, notNotEqual, selected,
    sharedSignedLess_whenComparing inputs comparing]

theorem comparisonOutput_unsignedGreaterOrEqual (inputs : Values)
    (notEqual : inputs.instr_beq = false) (notNotEqual : inputs.instr_bne = false)
    (notSignedGe : inputs.instr_bge = false) (selected : inputs.instr_bgeu = true)
    (comparing : inputs.is_compare = true) :
    comparisonOutput inputs = !(unsignedLessThan inputs.reg_op1 inputs.reg_op2) := by
  simp [comparisonOutput, notEqual, notNotEqual, notSignedGe, selected,
    sharedUnsignedLess_whenComparing inputs comparing]

theorem comparisonOutput_signedLessThan (inputs : Values)
    (notEqual : inputs.instr_beq = false) (notNotEqual : inputs.instr_bne = false)
    (notSignedGe : inputs.instr_bge = false) (notUnsignedGe : inputs.instr_bgeu = false)
    (selected : inputs.is_slti_blt_slt = true) (comparing : inputs.is_compare = true) :
    comparisonOutput inputs = signedLessThan inputs.reg_op1 inputs.reg_op2 := by
  simp [comparisonOutput, notEqual, notNotEqual, notSignedGe, notUnsignedGe, selected,
    sharedSignedLess_whenComparing inputs comparing]

theorem comparisonOutput_unsignedLessThan (inputs : Values)
    (notEqual : inputs.instr_beq = false) (notNotEqual : inputs.instr_bne = false)
    (notSignedGe : inputs.instr_bge = false) (notUnsignedGe : inputs.instr_bgeu = false)
    (notSignedLt : inputs.is_slti_blt_slt = false)
    (selected : inputs.is_sltiu_bltu_sltu = true) (comparing : inputs.is_compare = true) :
    comparisonOutput inputs = unsignedLessThan inputs.reg_op1 inputs.reg_op2 := by
  simp [comparisonOutput, notEqual, notNotEqual, notSignedGe, notUnsignedGe,
    notSignedLt, selected, sharedUnsignedLess_whenComparing inputs comparing]

/-- With no comparison condition selected, the independent comparison output is false. -/
theorem comparisonOutput_noSelection (inputs : Values)
    (notEqual : inputs.instr_beq = false) (notNotEqual : inputs.instr_bne = false)
    (notSignedGe : inputs.instr_bge = false) (notUnsignedGe : inputs.instr_bgeu = false)
    (notSignedLt : inputs.is_slti_blt_slt = false)
    (notUnsignedLt : inputs.is_sltiu_bltu_sltu = false) :
    comparisonOutput inputs = false := by
  simp [comparisonOutput, notEqual, notNotEqual, notSignedGe, notUnsignedGe,
    notSignedLt, notUnsignedLt]

end PicoRV.Alu
