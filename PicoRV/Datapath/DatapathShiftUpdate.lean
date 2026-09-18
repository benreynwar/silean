import PicoRV.Datapath.DatapathNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.AddSub.AddSub
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

def ShiftUpdate.amountSplitter : Silean.Composition.SignalSplitter := .vector 5 .bit

def ShiftUpdate.leftLayout (amount : Nat) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if low : index.val < amount then .constant false
  else .input ⟨index.val - amount, by omega⟩

def ShiftUpdate.rightLogicalLayout (amount : Nat) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if high : index.val + amount < 32 then .input ⟨index.val + amount, high⟩
  else .constant false

def ShiftUpdate.rightArithmeticLayout (amount : Nat) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if high : index.val + amount < 32 then .input ⟨index.val + amount, high⟩
  else .input ⟨31, by omega⟩

/-! One source shift step. Amount zero finishes by copying the current operand
to `reg_out`. A nonzero amount shifts by four when any high count bit is set,
and by one otherwise, then decrements the remaining count by the same amount.
Selector muxes preserve the source order left, logical right, arithmetic right.
-/
module_design ShiftUpdate (name := "picorv32_datapath_shift_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    currentFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    amountBits := Naming.SignalAdapter.splitterDesign ShiftUpdate.amountSplitter,
    amountHigh23 := Silean.Primitives.orDesign,
    amountGeFour := Silean.Primitives.orDesign,
    amountZero := Silean.Modules.EqualsConstant.design (.vector 5 .bit)
      (fiveBitsOfNat 0),
    leftSelect := Silean.Primitives.orDesign,
    logicalSelect := Silean.Primitives.orDesign,
    arithmeticSelect := Silean.Primitives.orDesign,
    trueBit := Silean.Modules.Constant.design .bit true,
    leftOne := Silean.Modules.VectorLayout.design 32 32 (ShiftUpdate.leftLayout 1),
    leftFour := Silean.Modules.VectorLayout.design 32 32 (ShiftUpdate.leftLayout 4),
    logicalOne := Silean.Modules.VectorLayout.design 32 32
      (ShiftUpdate.rightLogicalLayout 1),
    logicalFour := Silean.Modules.VectorLayout.design 32 32
      (ShiftUpdate.rightLogicalLayout 4),
    arithmeticOne := Silean.Modules.VectorLayout.design 32 32
      (ShiftUpdate.rightArithmeticLayout 1),
    arithmeticFour := Silean.Modules.VectorLayout.design 32 32
      (ShiftUpdate.rightArithmeticLayout 4),
    selectedLeft := Silean.Modules.Mux.design (.vector 32 .bit),
    selectedLogical := Silean.Modules.Mux.design (.vector 32 .bit),
    selectedArithmetic := Silean.Modules.Mux.design (.vector 32 .bit),
    selectArithmetic := Silean.Modules.Mux.design (.vector 32 .bit),
    selectLogical := Silean.Modules.Mux.design (.vector 32 .bit),
    selectLeft := Silean.Modules.Mux.design (.vector 32 .bit),
    one := Silean.Modules.Constant.design (.vector 5 .bit) (fiveBitsOfNat 1),
    four := Silean.Modules.Constant.design (.vector 5 .bit) (fiveBitsOfNat 4),
    selectedStep := Silean.Modules.Mux.design (.vector 5 .bit),
    subtractStep := Silean.Modules.AddSub.design 5,
    selectedOp1 := Silean.Modules.Mux.design (.vector 32 .bit),
    selectedShift := Silean.Modules.Mux.design (.vector 5 .bit),
    selectedResult := Silean.Modules.Mux.design (.vector 32 .bit),
    result := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.amountBits) { .value := currentFields[.reg_sh] }
  instance (.amountHigh23) {
    .left := amountBits[(2 : Fin 5)], .right := amountBits[(3 : Fin 5)] }
  instance (.amountGeFour) {
    .left := amountHigh23.output, .right := amountBits[(4 : Fin 5)] }
  instance (.amountZero) { .value := currentFields[.reg_sh] }
  instance (.leftSelect) {
    .left := inputsFields[.instr_slli], .right := inputsFields[.instr_sll] }
  instance (.logicalSelect) {
    .left := inputsFields[.instr_srli], .right := inputsFields[.instr_srl] }
  instance (.arithmeticSelect) {
    .left := inputsFields[.instr_srai], .right := inputsFields[.instr_sra] }
  instance (.trueBit) {}
  instance (.leftOne) { .input := currentFields[.reg_op1] }
  instance (.leftFour) { .input := currentFields[.reg_op1] }
  instance (.logicalOne) { .input := currentFields[.reg_op1] }
  instance (.logicalFour) { .input := currentFields[.reg_op1] }
  instance (.arithmeticOne) { .input := currentFields[.reg_op1] }
  instance (.arithmeticFour) { .input := currentFields[.reg_op1] }
  instance (.selectedLeft) {
    .select := amountGeFour.output,
    .whenFalse := leftOne.output, .whenTrue := leftFour.output }
  instance (.selectedLogical) {
    .select := amountGeFour.output,
    .whenFalse := logicalOne.output, .whenTrue := logicalFour.output }
  instance (.selectedArithmetic) {
    .select := amountGeFour.output,
    .whenFalse := arithmeticOne.output, .whenTrue := arithmeticFour.output }
  instance (.selectArithmetic) {
    .select := arithmeticSelect.output,
    .whenFalse := currentFields[.reg_op1],
    .whenTrue := selectedArithmetic.result }
  instance (.selectLogical) {
    .select := logicalSelect.output,
    .whenFalse := selectArithmetic.result,
    .whenTrue := selectedLogical.result }
  instance (.selectLeft) {
    .select := leftSelect.output,
    .whenFalse := selectLogical.result,
    .whenTrue := selectedLeft.result }
  instance (.one) {}
  instance (.four) {}
  instance (.selectedStep) {
    .select := amountGeFour.output,
    .whenFalse := one.output, .whenTrue := four.output }
  instance (.subtractStep) {
    .left := currentFields[.reg_sh],
    .right := selectedStep.result,
    .subtract := trueBit.output }
  instance (.selectedOp1) {
    .select := amountZero.result,
    .whenFalse := selectLeft.result,
    .whenTrue := updatedFields[.reg_op1] }
  instance (.selectedShift) {
    .select := amountZero.result,
    .whenFalse := subtractStep.result,
    .whenTrue := updatedFields[.reg_sh] }
  instance (.selectedResult) {
    .select := amountZero.result,
    .whenFalse := updatedFields[.reg_out],
    .whenTrue := currentFields[.reg_op1] }
  instance (.result) {
    .reg_pc := updatedFields[.reg_pc],
    .reg_next_pc := updatedFields[.reg_next_pc],
    .reg_op1 := selectedOp1.result,
    .reg_op2 := updatedFields[.reg_op2],
    .reg_out := selectedResult.result,
    .reg_sh := selectedShift.result,
    .alu_out_q := updatedFields[.alu_out_q] }
  }

end PicoRV.Datapath
