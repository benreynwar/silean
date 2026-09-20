import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.Internal.DatapathLoadRs1UpdateStructure
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring

/-! # First-operand capture

The mux chains are written from the default case upward and end with the trap
case. That order is the priority of the Verilog `case (1'b1)` when decoder
predicates overlap. -/

namespace LoadRs1Update.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let currentFields ← split DatapathState.layout current
  let updatedFields ← split DatapathState.layout updated
  let zeroWord ← constant (.vector 32 .bit) (wordOfNat 0)
  let lowFiveRs2 ← Silean.Modules.VectorLayout.place
    LoadRs1Update.lowFiveLayout (inputsFields .cpuregs_rs2)

  let luiOperand ← mux (inputsFields .instr_lui) (currentFields .reg_pc) zeroWord
  let selectedOp1 ← mux (inputsFields .is_lui_auipc_jal)
    (inputsFields .cpuregs_rs1) luiOperand
  let selectedOp1 ← mux (inputsFields .instr_trap)
    selectedOp1 (updatedFields .reg_op1)

  let selectedOp2 ← mux
    (inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi)
    (inputsFields .cpuregs_rs2) (inputsFields .decoded_imm)
  let selectedOp2 ← mux (inputsFields .is_slli_srli_srai)
    selectedOp2 (updatedFields .reg_op2)
  let selectedOp2 ← mux (inputsFields .is_lb_lh_lw_lbu_lhu)
    selectedOp2 (updatedFields .reg_op2)
  let selectedOp2 ← mux (inputsFields .is_lui_auipc_jal)
    selectedOp2 (inputsFields .decoded_imm)
  let selectedOp2 ← mux (inputsFields .instr_trap)
    selectedOp2 (updatedFields .reg_op2)

  let selectedShift ← mux
    (inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi)
    lowFiveRs2 (updatedFields .reg_sh)
  let selectedShift ← mux (inputsFields .is_slli_srli_srai)
    selectedShift (inputsFields .decoded_rs2)
  let selectedShift ← mux (inputsFields .is_lb_lh_lw_lbu_lhu)
    selectedShift (updatedFields .reg_sh)
  let selectedShift ← mux (inputsFields .is_lui_auipc_jal)
    selectedShift (updatedFields .reg_sh)
  let selectedShift ← mux (inputsFields .instr_trap)
    selectedShift (updatedFields .reg_sh)

  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_op1 => some selectedOp1
    | .reg_op2 => some selectedOp2
    | .reg_sh => some selectedShift
    | _ => none)

noncomputable def description : Description := build construction

end LoadRs1Update.Description

namespace LoadRs1Update

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "datapath_load_rs1_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end LoadRs1Update

end PicoRV.Datapath
