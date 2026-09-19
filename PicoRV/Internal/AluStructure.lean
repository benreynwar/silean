import Silean.Authoring.ModuleDesign
import Silean.Foundation.BitVector
import Silean.Modules.AddSub.AddSub
import Silean.Modules.BitMux.BitMux
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality
import Silean.Modules.Mux.Mux
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Not
import Silean.Primitives.Or
import Silean.Primitives.Xor

/-! Expanded typed hierarchy for the PicoRV ALU.

The readable dataflow and exact combinational contract live in
`PicoRV/Alu.lean`; this file supplies the representation used by structural
verification and emission. -/

namespace PicoRV.Alu

open Silean
open Silean.Authoring

abbrev Word := Fin 32 → Bool

module_ports ports where
  input reg_op1 : .vector 32 .bit,
  input reg_op2 : .vector 32 .bit,
  input instr_sub : .bit,
  input instr_beq : .bit,
  input instr_bne : .bit,
  input instr_bge : .bit,
  input instr_bgeu : .bit,
  input is_slti_blt_slt : .bit,
  input is_sltiu_bltu_sltu : .bit,
  input is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  input is_compare : .bit,
  input instr_xori : .bit,
  input instr_xor : .bit,
  input instr_ori : .bit,
  input instr_or : .bit,
  input instr_andi : .bit,
  input instr_and : .bit,
  output alu_out : .vector 32 .bit,
  output alu_out_0 : .bit

abbrev wordType : SignalType := .vector 32 .bit
abbrev wordSplitter : Silean.Composition.SignalSplitter := .vector 32 .bit
abbrev wordCombiner : Silean.Composition.SignalCombiner := .vector 32 .bit
def zeroBitValue : Bool := false
def zeroWordValue : Word := Silean.BitVector.ofNat 32 0

end PicoRV.Alu

namespace PicoRV

open Silean
open Silean.Authoring

module_design Alu (name := "picorv32_alu") where
  boundary (Alu.ports) (naming := Alu.Naming.ports)
  instances {
    leftSplit (name := .indexed "vector_splitter" 0) :=
      Naming.SignalAdapter.splitterDesign Alu.wordSplitter,
    rightSplit (name := .indexed "vector_splitter" 1) :=
      Naming.SignalAdapter.splitterDesign Alu.wordSplitter,
    subtractMode (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    addSub (name := .indexed "add_sub" 0) := Silean.Modules.AddSub.design 32,
    equality (name := .indexed "equality" 0) :=
      Silean.Modules.Equality.design Alu.wordType,
    bitwiseXor (name := .indexed "bitwise_xor" 0) :=
      Silean.Modules.BitwiseXor.design Alu.wordType,
    bitwiseOr (name := .indexed "bitwise_or" 0) :=
      Silean.Modules.BitwiseOr.design Alu.wordType,
    bitwiseAnd (name := .indexed "bitwise_and" 0) :=
      Silean.Modules.BitwiseAnd.design Alu.wordType,
    zeroBit (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design .bit Alu.zeroBitValue,
    zeroWord (name := .indexed "constant" 1) :=
      Silean.Modules.Constant.design Alu.wordType Alu.zeroWordValue,
    unsignedLess (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    signDifference (name := .indexed "xor" 0) := Silean.Primitives.xorDesign,
    signedLess (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    notEqual (name := .indexed "not" 1) := Silean.Primitives.notDesign,
    notSignedLess (name := .indexed "not" 2) := Silean.Primitives.notDesign,
    notUnsignedLess (name := .indexed "not" 3) := Silean.Primitives.notDesign,
    selectUnsignedLess (name := .indexed "bit_mux" 1) := Silean.Modules.BitMux.design,
    selectSignedLess (name := .indexed "bit_mux" 2) := Silean.Modules.BitMux.design,
    selectUnsignedGreaterEqual (name := .indexed "bit_mux" 3) :=
      Silean.Modules.BitMux.design,
    selectSignedGreaterEqual (name := .indexed "bit_mux" 4) :=
      Silean.Modules.BitMux.design,
    selectNotEqual (name := .indexed "bit_mux" 5) := Silean.Modules.BitMux.design,
    selectEqual (name := .indexed "bit_mux" 6) := Silean.Modules.BitMux.design,
    comparisonWord (name := .indexed "combiner" 0) :=
      Naming.SignalAdapter.combinerDesign Alu.wordCombiner,
    xorSelected (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    orSelected (name := .indexed "or" 2) := Silean.Primitives.orDesign,
    andSelected (name := .indexed "or" 3) := Silean.Primitives.orDesign,
    selectAnd (name := .indexed "mux" 0) := Silean.Modules.Mux.design Alu.wordType,
    selectOr (name := .indexed "mux" 1) := Silean.Modules.Mux.design Alu.wordType,
    selectXor (name := .indexed "mux" 2) := Silean.Modules.Mux.design Alu.wordType,
    selectComparison (name := .indexed "mux" 3) :=
      Silean.Modules.Mux.design Alu.wordType,
    selectArithmetic (name := .indexed "mux" 4) :=
      Silean.Modules.Mux.design Alu.wordType }
  wiring {
    outputs {
      .alu_out := selectArithmetic.result,
      .alu_out_0 := selectEqual.result }
    instance (.leftSplit) { .value := input.reg_op1 }
    instance (.rightSplit) { .value := input.reg_op2 }
    instance (.subtractMode) { .left := input.instr_sub, .right := input.is_compare }
    instance (.addSub) {
      .left := input.reg_op1,
      .right := input.reg_op2,
      .subtract := subtractMode.output }
    instance (.equality) { .left := input.reg_op1, .right := input.reg_op2 }
    instance (.bitwiseXor) { .left := input.reg_op1, .right := input.reg_op2 }
    instance (.bitwiseOr) { .left := input.reg_op1, .right := input.reg_op2 }
    instance (.bitwiseAnd) { .left := input.reg_op1, .right := input.reg_op2 }
    instance (.zeroBit) {}
    instance (.zeroWord) {}
    instance (.unsignedLess) { .input := addSub.carryOut }
    instance (.signDifference) {
      .left := leftSplit[Fin.last 31],
      .right := rightSplit[Fin.last 31] }
    instance (.signedLess) {
      .select := signDifference.output,
      .whenFalse := unsignedLess.output,
      .whenTrue := leftSplit[Fin.last 31] }
    instance (.notEqual) { .input := equality.result }
    instance (.notSignedLess) { .input := signedLess.result }
    instance (.notUnsignedLess) { .input := unsignedLess.output }
    instance (.selectUnsignedLess) {
      .select := input.is_sltiu_bltu_sltu,
      .whenFalse := zeroBit.output,
      .whenTrue := unsignedLess.output }
    instance (.selectSignedLess) {
      .select := input.is_slti_blt_slt,
      .whenFalse := selectUnsignedLess.result,
      .whenTrue := signedLess.result }
    instance (.selectUnsignedGreaterEqual) {
      .select := input.instr_bgeu,
      .whenFalse := selectSignedLess.result,
      .whenTrue := notUnsignedLess.output }
    instance (.selectSignedGreaterEqual) {
      .select := input.instr_bge,
      .whenFalse := selectUnsignedGreaterEqual.result,
      .whenTrue := notSignedLess.output }
    instance (.selectNotEqual) {
      .select := input.instr_bne,
      .whenFalse := selectSignedGreaterEqual.result,
      .whenTrue := notEqual.output }
    instance (.selectEqual) {
      .select := input.instr_beq,
      .whenFalse := selectNotEqual.result,
      .whenTrue := equality.result }
    instance (.comparisonWord) {
      index := from (if (show Fin 32 from index) = 0 then
        c.instanceOutput .selectEqual .result
      else c.instanceOutput .zeroBit .output) }
    instance (.xorSelected) { .left := input.instr_xori, .right := input.instr_xor }
    instance (.orSelected) { .left := input.instr_ori, .right := input.instr_or }
    instance (.andSelected) { .left := input.instr_andi, .right := input.instr_and }
    instance (.selectAnd) {
      .select := andSelected.output,
      .whenFalse := zeroWord.output,
      .whenTrue := bitwiseAnd.result }
    instance (.selectOr) {
      .select := orSelected.output,
      .whenFalse := selectAnd.result,
      .whenTrue := bitwiseOr.result }
    instance (.selectXor) {
      .select := xorSelected.output,
      .whenFalse := selectOr.result,
      .whenTrue := bitwiseXor.result }
    instance (.selectComparison) {
      .select := input.is_compare,
      .whenFalse := selectXor.result,
      .whenTrue := comparisonWord.value }
    instance (.selectArithmetic) {
      .select := input.is_lui_auipc_jal_jalr_addi_add_sub,
      .whenFalse := selectComparison.result,
      .whenTrue := addSub.result }
  }

end PicoRV
