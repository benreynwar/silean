import Silean.FIRRTL
import PicoRV.AluTheorems

namespace PicoRVTests.Alu

open Silean Silean.FIRRTL PicoRV

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified Alu.ports :=
  Alu.certified

example : Alu.outputRule.readsInputs.labels =
    Alu.ports.inputs.labels.values := by
  change (Silean.SignalGroup.all Alu.ports.inputs).labels = _
  exact Silean.SignalGroup.all_labels _

example : Alu.outputRule.writesOutputs.labels =
    Alu.ports.outputs.labels.values := by
  change (Silean.SignalGroup.all Alu.ports.outputs).labels = _
  exact Silean.SignalGroup.all_labels _

private def base (left right : Alu.Word) : Alu.Values where
  reg_op1 := left
  reg_op2 := right
  instr_sub := false
  instr_beq := false
  instr_bne := false
  instr_bge := false
  instr_bgeu := false
  is_slti_blt_slt := false
  is_sltiu_bltu_sltu := false
  is_lui_auipc_jal_jalr_addi_add_sub := false
  is_compare := false
  instr_xori := false
  instr_xor := false
  instr_ori := false
  instr_or := false
  instr_andi := false
  instr_and := false

private def addInputs : Alu.Values :=
  { base (Alu.wordOfNat 7) (Alu.wordOfNat 9) with
    is_lui_auipc_jal_jalr_addi_add_sub := true }

private def subtractInputs : Alu.Values :=
  { base (Alu.wordOfNat 7) (Alu.wordOfNat 9) with
    instr_sub := true
    is_lui_auipc_jal_jalr_addi_add_sub := true }

private def signedLessInputs : Alu.Values :=
  { base (Alu.wordOfNat (2 ^ 32 - 1)) (Alu.wordOfNat 1) with
    is_slti_blt_slt := true
    is_compare := true }

#guard Silean.BitVector.toNat 32 (Alu.aluOut addInputs) == 16
#guard Silean.BitVector.toNat 32 (Alu.aluOut subtractInputs) == 2 ^ 32 - 2
#guard Alu.comparisonOutput signedLessInputs
#guard Alu.aluOut signedLessInputs 0
#guard !(Alu.aluOut signedLessInputs 1)
#guard Silean.BitVector.toNat 32 (Alu.aluOut (base (Alu.wordOfNat 7) (Alu.wordOfNat 9))) == 0
#guard !(Alu.comparisonOutput (base (Alu.wordOfNat 7) (Alu.wordOfNat 9)))

-- The closed renderer checks and accepts the concrete hierarchy.
noncomputable example : RenderResult String :=
  renderClosedCircuit Alu.naming

#guard renderModuleKey Alu.naming.key = "picorv32_alu"
#guard Alu.Naming.ports.inputs.name .reg_op1 = "reg_op1"
#guard Alu.Naming.ports.inputs.name .is_lui_auipc_jal_jalr_addi_add_sub =
  "is_lui_auipc_jal_jalr_addi_add_sub"
#guard Alu.Naming.ports.outputs.name .alu_out = "alu_out"
#guard Alu.Naming.ports.outputs.name .alu_out_0 = "alu_out_0"

end PicoRVTests.Alu
