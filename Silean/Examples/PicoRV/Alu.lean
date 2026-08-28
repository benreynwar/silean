import Silean.Foundation.BitVector
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Alu

open Silean

/-! Cycle contract for the combinational PicoRV32 ALU, retaining the port names
and operation-selection behavior of the target Verilog configuration. The
structural implementation has not yet been added. -/

abbrev Word := Fin 32 → Bool

inductive Input
  | reg_op1
  | reg_op2
  | instr_sub
  | instr_beq
  | instr_bne
  | instr_bge
  | instr_bgeu
  | is_slti_blt_slt
  | is_sltiu_bltu_sltu
  | is_lui_auipc_jal_jalr_addi_add_sub
  | is_compare
  | instr_xori
  | instr_xor
  | instr_ori
  | instr_or
  | instr_andi
  | instr_and
deriving Enumeration

inductive Output
  | alu_out
  | alu_out_0
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .reg_op1 | .reg_op2 => .vector 32 .bit
    | _ => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun
    | .alu_out => .vector 32 .bit
    | .alu_out_0 => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val

def wordOfBool (value : Bool) : Word := fun index =>
  if index = 0 then value else false

def addSub (instr_sub : Bool) (reg_op1 reg_op2 : Word) : Word :=
  let modulus := BitVector.cardinality 32
  let left := BitVector.toNat 32 reg_op1
  let right := BitVector.toNat 32 reg_op2
  if instr_sub then wordOfNat ((left + modulus - right) % modulus)
  else wordOfNat ((left + right) % modulus)

def equal (reg_op1 reg_op2 : Word) : Bool :=
  decide (BitVector.toNat 32 reg_op1 = BitVector.toNat 32 reg_op2)

def unsignedLessThan (reg_op1 reg_op2 : Word) : Bool :=
  decide (BitVector.toNat 32 reg_op1 < BitVector.toNat 32 reg_op2)

def signedLessThan (reg_op1 reg_op2 : Word) : Bool :=
  if reg_op1 31 = reg_op2 31 then unsignedLessThan reg_op1 reg_op2
  else reg_op1 31

def bitwiseXor (reg_op1 reg_op2 : Word) : Word :=
  fun index => Bool.xor (reg_op1 index) (reg_op2 index)

def bitwiseOr (reg_op1 reg_op2 : Word) : Word :=
  fun index => reg_op1 index || reg_op2 index

def bitwiseAnd (reg_op1 reg_op2 : Word) : Word :=
  fun index => reg_op1 index && reg_op2 index

structure Values where
  reg_op1 : Word
  reg_op2 : Word
  instr_sub : Bool
  instr_beq : Bool
  instr_bne : Bool
  instr_bge : Bool
  instr_bgeu : Bool
  is_slti_blt_slt : Bool
  is_sltiu_bltu_sltu : Bool
  is_lui_auipc_jal_jalr_addi_add_sub : Bool
  is_compare : Bool
  instr_xori : Bool
  instr_xor : Bool
  instr_ori : Bool
  instr_or : Bool
  instr_andi : Bool
  instr_and : Bool

inductive Comparison
  | equal
  | notEqual
  | signedGreaterOrEqual
  | unsignedGreaterOrEqual
  | signedLessThan
  | unsignedLessThan

inductive Operation
  | add
  | subtract
  | compare
  | bitwiseXor
  | bitwiseOr
  | bitwiseAnd

structure Result where
  alu_out : Word
  alu_out_0 : Bool

def selectedComparison (inputs : Values) : Comparison :=
  if inputs.instr_beq then .equal
  else if inputs.instr_bne then .notEqual
  else if inputs.instr_bge then .signedGreaterOrEqual
  else if inputs.instr_bgeu then .unsignedGreaterOrEqual
  else if inputs.is_slti_blt_slt then .signedLessThan
  else if inputs.is_sltiu_bltu_sltu then .unsignedLessThan
  else .equal

def selectedOperation (inputs : Values) : Operation :=
  let arithmetic := if inputs.instr_sub then Operation.subtract else .add
  if inputs.is_lui_auipc_jal_jalr_addi_add_sub then arithmetic
  else if inputs.is_compare then .compare
  else if inputs.instr_xori || inputs.instr_xor then .bitwiseXor
  else if inputs.instr_ori || inputs.instr_or then .bitwiseOr
  else if inputs.instr_andi || inputs.instr_and then .bitwiseAnd
  else arithmetic

def evaluateComparison (comparison : Comparison)
    (reg_op1 reg_op2 : Word) : Bool :=
  match comparison with
  | .equal => equal reg_op1 reg_op2
  | .notEqual => !(equal reg_op1 reg_op2)
  | .signedGreaterOrEqual => !(signedLessThan reg_op1 reg_op2)
  | .unsignedGreaterOrEqual => !(unsignedLessThan reg_op1 reg_op2)
  | .signedLessThan => signedLessThan reg_op1 reg_op2
  | .unsignedLessThan => unsignedLessThan reg_op1 reg_op2

def evaluateOperation (operation : Operation) (comparison : Bool)
    (reg_op1 reg_op2 : Word) : Word :=
  match operation with
  | .add => addSub false reg_op1 reg_op2
  | .subtract => addSub true reg_op1 reg_op2
  | .compare => wordOfBool comparison
  | .bitwiseXor => bitwiseXor reg_op1 reg_op2
  | .bitwiseOr => bitwiseOr reg_op1 reg_op2
  | .bitwiseAnd => bitwiseAnd reg_op1 reg_op2

def evaluate (inputs : Values) : Result :=
  let comparison := evaluateComparison (selectedComparison inputs)
    inputs.reg_op1 inputs.reg_op2
  {
    alu_out := evaluateOperation (selectedOperation inputs) comparison
      inputs.reg_op1 inputs.reg_op2
    alu_out_0 := comparison
  }

def aluOut (inputs : Values) : Word := (evaluate inputs).alu_out

def aluOut0 (inputs : Values) : Bool := (evaluate inputs).alu_out_0

inductive Rule | apply
deriving Enumeration

def outputRule :
    Contracts.Cycle.CycleOutputRule ports emptySignalMap
      { inputTypes := .cons (.vector 32 .bit)
          (.cons (.vector 32 .bit)
            (.cons .bit (.cons .bit (.cons .bit (.cons .bit (.cons .bit
              (.cons .bit (.cons .bit (.cons .bit (.cons .bit (.cons .bit
                (.cons .bit (.cons .bit (.cons .bit (.cons .bit
                  (.cons .bit .nil))))))))))))))))
        outputTypes := .cons (.vector 32 .bit) (.cons .bit .nil) } where
  readsInputs := ((((((((((((((((inputMap.select .instr_and).prepend
    .instr_andi).prepend .instr_or).prepend .instr_ori).prepend
    .instr_xor).prepend .instr_xori).prepend .is_compare).prepend
    .is_lui_auipc_jal_jalr_addi_add_sub).prepend
    .is_sltiu_bltu_sltu).prepend .is_slti_blt_slt).prepend
    .instr_bgeu).prepend .instr_bge).prepend .instr_bne).prepend
    .instr_beq).prepend .instr_sub).prepend .reg_op2).prepend .reg_op1
  writesOutputs := (outputMap.select .alu_out_0).prepend .alu_out
  target := fun values _ =>
    let inputs : Values := {
      reg_op1 := values.1
      reg_op2 := values.2.1
      instr_sub := values.2.2.1
      instr_beq := values.2.2.2.1
      instr_bne := values.2.2.2.2.1
      instr_bge := values.2.2.2.2.2.1
      instr_bgeu := values.2.2.2.2.2.2.1
      is_slti_blt_slt := values.2.2.2.2.2.2.2.1
      is_sltiu_bltu_sltu := values.2.2.2.2.2.2.2.2.1
      is_lui_auipc_jal_jalr_addi_add_sub := values.2.2.2.2.2.2.2.2.2.1
      is_compare := values.2.2.2.2.2.2.2.2.2.2.1
      instr_xori := values.2.2.2.2.2.2.2.2.2.2.2.1
      instr_xor := values.2.2.2.2.2.2.2.2.2.2.2.2.1
      instr_ori := values.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      instr_or := values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      instr_andi := values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      instr_and := values.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    }
    (aluOut inputs, (aluOut0 inputs, ()))

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

def valuesOf (inputs : ports.inputs.Values) : Values where
  reg_op1 := inputs .reg_op1
  reg_op2 := inputs .reg_op2
  instr_sub := inputs .instr_sub
  instr_beq := inputs .instr_beq
  instr_bne := inputs .instr_bne
  instr_bge := inputs .instr_bge
  instr_bgeu := inputs .instr_bgeu
  is_slti_blt_slt := inputs .is_slti_blt_slt
  is_sltiu_bltu_sltu := inputs .is_sltiu_bltu_sltu
  is_lui_auipc_jal_jalr_addi_add_sub :=
    inputs .is_lui_auipc_jal_jalr_addi_add_sub
  is_compare := inputs .is_compare
  instr_xori := inputs .instr_xori
  instr_xor := inputs .instr_xor
  instr_ori := inputs .instr_ori
  instr_or := inputs .instr_or
  instr_andi := inputs .instr_andi
  instr_and := inputs .instr_and

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .alu_out = aluOut (valuesOf inputs) ∧
      outputs .alu_out_0 = aluOut0 (valuesOf inputs) := by
  change (outputs .alu_out = aluOut (valuesOf inputs) ∧
    outputs .alu_out_0 = aluOut0 (valuesOf inputs) ∧ True) ↔ _
  simp

end Silean.Examples.PicoRV.Alu
