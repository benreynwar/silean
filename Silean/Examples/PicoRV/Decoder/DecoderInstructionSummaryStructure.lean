import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummary
import Silean.Authoring.ModuleDesign
import Silean.Modules.Any.Any
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Not

namespace Silean.Examples.PicoRV.Decoder.InstructionSummary

open Silean
open Silean.Authoring

/-! Each summary is an OR reduction of the instruction flags named by its
contract predicate. The illegal-instruction output inverts the reduction of
the 38 non-trapping instruction flags. In particular, the source deliberately
omits its separately decoded ECALL/EBREAK flag so those instructions enter the
trap path. Keeping these as separate children preserves the contract's
independent `trap` and `summaries` rules. -/

module_design Structure (name := "PicoRVDecoderInstructionSummary") where
  boundary (ports) (naming := Naming.ports)
  instances {
    recognized := Modules.Any.design 38,
    trap := Primitives.notDesign,
    luiAuipcJal := Modules.Any.design 3,
    arithmetic := Modules.Any.design 7,
    signedCompare := Modules.Any.design 3,
    unsignedCompare := Modules.Any.design 3,
    unsignedLoad := Modules.Any.design 3,
    compare := Modules.Any.design 5 }
  wiring {
  outputs {
    .instr_trap := trap.output,
    .is_lui_auipc_jal := luiAuipcJal.output,
    .is_lui_auipc_jal_jalr_addi_add_sub := arithmetic.output,
    .is_slti_blt_slt := signedCompare.output,
    .is_sltiu_bltu_sltu := unsignedCompare.output,
    .is_lbu_lhu_lw := unsignedLoad.output,
    .is_compare := compare.output }
  instance (.recognized) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_lui | 1 => c.moduleInput .instr_auipc
      | 2 => c.moduleInput .instr_jal | 3 => c.moduleInput .instr_jalr
      | 4 => c.moduleInput .instr_beq | 5 => c.moduleInput .instr_bne
      | 6 => c.moduleInput .instr_blt | 7 => c.moduleInput .instr_bge
      | 8 => c.moduleInput .instr_bltu | 9 => c.moduleInput .instr_bgeu
      | 10 => c.moduleInput .instr_lb | 11 => c.moduleInput .instr_lh
      | 12 => c.moduleInput .instr_lw | 13 => c.moduleInput .instr_lbu
      | 14 => c.moduleInput .instr_lhu | 15 => c.moduleInput .instr_sb
      | 16 => c.moduleInput .instr_sh | 17 => c.moduleInput .instr_sw
      | 18 => c.moduleInput .instr_addi | 19 => c.moduleInput .instr_slti
      | 20 => c.moduleInput .instr_sltiu | 21 => c.moduleInput .instr_xori
      | 22 => c.moduleInput .instr_ori | 23 => c.moduleInput .instr_andi
      | 24 => c.moduleInput .instr_slli | 25 => c.moduleInput .instr_srli
      | 26 => c.moduleInput .instr_srai | 27 => c.moduleInput .instr_add
      | 28 => c.moduleInput .instr_sub | 29 => c.moduleInput .instr_sll
      | 30 => c.moduleInput .instr_slt | 31 => c.moduleInput .instr_sltu
      | 32 => c.moduleInput .instr_xor | 33 => c.moduleInput .instr_srl
      | 34 => c.moduleInput .instr_sra | 35 => c.moduleInput .instr_or
      | 36 => c.moduleInput .instr_and
      | _ => c.moduleInput .instr_fence) }
  instance (.trap) { .input := recognized.output }
  instance (.luiAuipcJal) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_lui
      | 1 => c.moduleInput .instr_auipc
      | _ => c.moduleInput .instr_jal) }
  instance (.arithmetic) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_lui | 1 => c.moduleInput .instr_auipc
      | 2 => c.moduleInput .instr_jal | 3 => c.moduleInput .instr_jalr
      | 4 => c.moduleInput .instr_addi | 5 => c.moduleInput .instr_add
      | _ => c.moduleInput .instr_sub) }
  instance (.signedCompare) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_slti
      | 1 => c.moduleInput .instr_blt
      | _ => c.moduleInput .instr_slt) }
  instance (.unsignedCompare) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_sltiu
      | 1 => c.moduleInput .instr_bltu
      | _ => c.moduleInput .instr_sltu) }
  instance (.unsignedLoad) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .instr_lbu
      | 1 => c.moduleInput .instr_lhu
      | _ => c.moduleInput .instr_lw) }
  instance (.compare) {
    (.leaf index) := from (match index.val with
      | 0 => c.moduleInput .is_beq_bne_blt_bge_bltu_bgeu
      | 1 => c.moduleInput .instr_slti | 2 => c.moduleInput .instr_slt
      | 3 => c.moduleInput .instr_sltiu
      | _ => c.moduleInput .instr_sltu) }
  }

end Silean.Examples.PicoRV.Decoder.InstructionSummary
