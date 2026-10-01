import PicoRV.Internal.AluVerification

namespace PicoRV.Alu

open Silean
open Silean.Authoring.CircuitDescription

/-! Public ALU declarations backed by generated internals. -/

abbrev InputNets :=
  (input : ports.inputs.Label) → Net (ports.inputs.signalType input)

/-- Place an ALU using the next conventional indexed name. -/
noncomputable def place (inputs : InputNets) : Builder ports.OutputNets := do
  let child ← Silean.Authoring.CircuitDescription.placeIndexed
    "alu" design inputs
  pure (ports.OutputNets.ofFn child)

/-- Place an ALU under an explicitly chosen structural name. -/
noncomputable def placeNamed (name : Naming.SourceName) (inputs : InputNets) :
    Builder ports.OutputNets := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed
    name design inputs
  pure (ports.OutputNets.ofFn child)

attribute [circuit_description] place placeNamed

/-- Every typed implementation corresponding to the authored ALU construction
implements its exact cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

@[simp] theorem aluOut0_eq (inputs : Values) :
    aluOut0 inputs = comparisonOutput inputs := rfl

theorem sharedUnsignedLess_whenComparing (inputs : Values)
    (comparing : inputs.is_compare = true) :
    sharedUnsignedLess inputs = unsignedLessThan inputs.reg_op1 inputs.reg_op2 := by
  unfold sharedUnsignedLess unsignedLessThan
  rw [show (inputs.instr_sub || inputs.is_compare) = true by simp [comparing]]
  rw [Silean.Modules.AddSubWithCarry.addSubBits_carry_subtract]
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
