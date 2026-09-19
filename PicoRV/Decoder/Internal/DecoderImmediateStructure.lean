import PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Or

/-! Expanded typed hierarchy and concrete bit layouts for immediate decoding. -/

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open PicoRV.Decoder

module_ports ports where
  input word : .vector 32 .bit,
  input decoded_imm_j : .vector 32 .bit,
  input instr_jal : .bit,
  input instr_lui : .bit,
  input instr_auipc : .bit,
  input instr_jalr : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_alu_reg_imm : .bit,
  input is_beq_bne_blt_bge_bltu_bgeu : .bit,
  input is_sb_sh_sw : .bit,
  output valid : .bit,
  output value : .vector 32 .bit

def immediateILayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 12 then .input ⟨index.val + 20, by omega⟩
  else .input ⟨31, by omega⟩

def immediateULayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 12 then .constant false else .input index

def immediateSLayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 5 then .input ⟨index.val + 7, by omega⟩
  else if _middle : index.val < 12 then .input ⟨index.val + 20, by omega⟩
  else .input ⟨31, by omega⟩

def immediateBLayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _zero : index.val = 0 then .constant false
  else if _low : index.val < 5 then .input ⟨index.val + 7, by omega⟩
  else if _middle : index.val < 11 then .input ⟨index.val + 20, by omega⟩
  else if _eleven : index.val = 11 then .input ⟨7, by omega⟩
  else .input ⟨31, by omega⟩

end PicoRV.Decoder.Immediate

namespace PicoRV.Decoder

open Silean
open Silean.Authoring

module_design Immediate (name := "picorv32_decoder_immediate") where
  boundary (Immediate.ports) (naming := Immediate.Naming.ports)
  instances {
    immediateI (name := .indexed "vector_layout" 0) :=
      Silean.Modules.VectorLayout.design 32 32 Immediate.immediateILayout,
    immediateU (name := .indexed "vector_layout" 1) :=
      Silean.Modules.VectorLayout.design 32 32 Immediate.immediateULayout,
    immediateS (name := .indexed "vector_layout" 2) :=
      Silean.Modules.VectorLayout.design 32 32 Immediate.immediateSLayout,
    immediateB (name := .indexed "vector_layout" 3) :=
      Silean.Modules.VectorLayout.design 32 32 Immediate.immediateBLayout,
    uSelected (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    iSelectedPartial (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    iSelected (name := .indexed "or" 2) := Silean.Primitives.orDesign,
    lowerValid (name := .indexed "or" 3) := Silean.Primitives.orDesign,
    iOrLowerValid (name := .indexed "or" 4) := Silean.Primitives.orDesign,
    uOrLowerValid (name := .indexed "or" 5) := Silean.Primitives.orDesign,
    validGate (name := .indexed "or" 6) := Silean.Primitives.orDesign,
    zero (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design (.vector 32 .bit) (fun _ => false),
    selectS (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectB (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectI (name := .indexed "mux" 2) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectU (name := .indexed "mux" 3) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectJ (name := .indexed "mux" 4) := Silean.Modules.Mux.design (.vector 32 .bit) }
  wiring {
    outputs { .valid := validGate.output, .value := selectJ.result }
    instance (.immediateI) { .input := input.word }
    instance (.immediateU) { .input := input.word }
    instance (.immediateS) { .input := input.word }
    instance (.immediateB) { .input := input.word }
    instance (.uSelected) { .left := input.instr_lui, .right := input.instr_auipc }
    instance (.iSelectedPartial) {
      .left := input.instr_jalr,
      .right := input.is_lb_lh_lw_lbu_lhu }
    instance (.iSelected) {
      .left := iSelectedPartial.output,
      .right := input.is_alu_reg_imm }
    instance (.lowerValid) {
      .left := input.is_beq_bne_blt_bge_bltu_bgeu,
      .right := input.is_sb_sh_sw }
    instance (.iOrLowerValid) { .left := iSelected.output, .right := lowerValid.output }
    instance (.uOrLowerValid) { .left := uSelected.output, .right := iOrLowerValid.output }
    instance (.validGate) { .left := input.instr_jal, .right := uOrLowerValid.output }
    instance (.zero) {}
    instance (.selectS) {
      .select := input.is_sb_sh_sw,
      .whenFalse := zero.output,
      .whenTrue := immediateS.output }
    instance (.selectB) {
      .select := input.is_beq_bne_blt_bge_bltu_bgeu,
      .whenFalse := selectS.result,
      .whenTrue := immediateB.output }
    instance (.selectI) {
      .select := iSelected.output,
      .whenFalse := selectB.result,
      .whenTrue := immediateI.output }
    instance (.selectU) {
      .select := uSelected.output,
      .whenFalse := selectI.result,
      .whenTrue := immediateU.output }
    instance (.selectJ) {
      .select := input.instr_jal,
      .whenFalse := selectU.result,
      .whenTrue := input.decoded_imm_j }
  }

end PicoRV.Decoder
