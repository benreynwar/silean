import PicoRV.Datapath.DatapathNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.AddDerived
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

def MemoryUpdateCore.signExtendLayout (width : Nat) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if low : index.val < width then .input index
  else .input ⟨width - 1, by omega⟩

/-! Shared effective-address and completion datapath for store and load phases.
The request kind is explicit so the same proved circuit can be specialized by
the two source-region wrappers below. -/
module_design MemoryUpdateCore (name := "picorv32_datapath_memory_update") where
  boundary (MemoryUpdateCore.ports) (naming := MemoryUpdateCore.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    zeroWord (name := .indexed "constant" 1) := Silean.Modules.Constant.design (.vector 32 .bit) (wordOfNat 0),
    notPrefetch (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    progress (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    active (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    notActive (name := .indexed "not" 1) := Silean.Primitives.notDesign,
    effectiveAddress (name := .indexed "add" 0) := Silean.Modules.Add.design 32,
    effectiveOp1 (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectedOp1 (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 32 .bit),
    signedHalf (name := .indexed "vector_layout" 0) := Silean.Modules.VectorLayout.design 32 32
      (MemoryUpdateCore.signExtendLayout 16),
    signedByte (name := .indexed "vector_layout" 1) := Silean.Modules.VectorLayout.design 32 32
      (MemoryUpdateCore.signExtendLayout 8),
    selectByte (name := .indexed "mux" 2) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectHalf (name := .indexed "mux" 3) := Silean.Modules.Mux.design (.vector 32 .bit),
    selectUnsigned (name := .indexed "mux" 4) := Silean.Modules.Mux.design (.vector 32 .bit),
    loadDoneLeft (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    loadDone (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    selectedResult (name := .indexed "mux" 5) := Silean.Modules.Mux.design (.vector 32 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.zeroWord) {}
  instance (.notPrefetch) { .input := inputsFields[.mem_do_prefetch] }
  instance (.progress) {
    .left := notPrefetch.output, .right := inputsFields[.mem_done] }
  instance (.active) {
    .select := input.isLoad,
    .whenFalse := inputsFields[.mem_do_wdata],
    .whenTrue := inputsFields[.mem_do_rdata] }
  instance (.notActive) { .input := active.result }
  instance (.effectiveAddress) {
    .left := currentFields[.reg_op1],
    .right := inputsFields[.decoded_imm],
    .carryIn := falseBit.output }
  instance (.effectiveOp1) {
    .select := notActive.output,
    .whenFalse := updatedFields[.reg_op1],
    .whenTrue := effectiveAddress.result }
  instance (.selectedOp1) {
    .select := progress.output,
    .whenFalse := updatedFields[.reg_op1],
    .whenTrue := effectiveOp1.result }
  instance (.signedHalf) { .input := inputsFields[.mem_rdata_word] }
  instance (.signedByte) { .input := inputsFields[.mem_rdata_word] }
  instance (.selectByte) {
    .select := inputsFields[.latched_is_lb],
    .whenFalse := zeroWord.output,
    .whenTrue := signedByte.output }
  instance (.selectHalf) {
    .select := inputsFields[.latched_is_lh],
    .whenFalse := selectByte.result,
    .whenTrue := signedHalf.output }
  instance (.selectUnsigned) {
    .select := inputsFields[.latched_is_lu],
    .whenFalse := selectHalf.result,
    .whenTrue := inputsFields[.mem_rdata_word] }
  instance (.loadDoneLeft) {
    .left := input.isLoad, .right := notPrefetch.output }
  instance (.loadDone) {
    .left := loadDoneLeft.output, .right := inputsFields[.mem_done] }
  instance (.selectedResult) {
    .select := loadDone.output,
    .whenFalse := updatedFields[.reg_out],
    .whenTrue := selectUnsigned.result }
  instance (.result) {
    .reg_pc := updatedFields[.reg_pc],
    .reg_next_pc := updatedFields[.reg_next_pc],
    .reg_op1 := selectedOp1.result,
    .reg_op2 := updatedFields[.reg_op2],
    .reg_out := selectedResult.result,
    .reg_sh := updatedFields[.reg_sh],
    .alu_out_q := updatedFields[.alu_out_q] }
  }

module_design StoreUpdate (name := "picorv32_datapath_store_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    isLoad (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    update (name := .indexed "datapath_memory_update" 0) := MemoryUpdateCore.design }
  wiring {
  outputs { .state := update.state }
  instance (.isLoad) {}
  instance (.update) {
    .isLoad := isLoad.output,
    .inputs := input.inputs,
    .current := input.current,
    .updated := input.updated }
  }

module_design LoadUpdate (name := "picorv32_datapath_load_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    isLoad (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit true,
    update (name := .indexed "datapath_memory_update" 0) := MemoryUpdateCore.design }
  wiring {
  outputs { .state := update.state }
  instance (.isLoad) {}
  instance (.update) {
    .isLoad := isLoad.output,
    .inputs := input.inputs,
    .current := input.current,
    .updated := input.updated }
  }

end PicoRV.Datapath
