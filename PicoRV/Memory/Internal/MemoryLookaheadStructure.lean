import PicoRV.Memory.MemoryCombinationalContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Primitives.And
import Silean.Primitives.Or

namespace PicoRV.Memory

open Silean
open Silean.Authoring

def Lookahead.alignedLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if index.val < 2 then .constant false else .input index

def Lookahead.halfDataLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val % 16, by omega⟩

def Lookahead.byteDataLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val % 8, by omega⟩

/-! Expanded typed production structure for the reader-facing look-ahead
definition in `MemoryLookahead.lean`. -/
module_design Lookahead (name := "picorv32_memory_lookahead") where
  boundary (Lookahead.ports) (naming := Lookahead.Naming.ports)
  instances {
    currentFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    idle (name := .indexed "equals_constant" 0) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 0),
    enabledIdle (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    instructionCommand (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    readCommand (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    read (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    write (name := .indexed "and" 2) := Silean.Primitives.andDesign,
    alignedNextPc (name := .indexed "vector_layout" 0) :=
      Silean.Modules.VectorLayout.design 32 32 Lookahead.alignedLayout,
    alignedRegOp1 (name := .indexed "vector_layout" 1) :=
      Silean.Modules.VectorLayout.design 32 32 Lookahead.alignedLayout,
    address (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design (.vector 32 .bit),
    halfData (name := .indexed "vector_layout" 2) :=
      Silean.Modules.VectorLayout.design 32 32 Lookahead.halfDataLayout,
    byteData (name := .indexed "vector_layout" 3) :=
      Silean.Modules.VectorLayout.design 32 32 Lookahead.byteDataLayout,
    halfWordsize (name := .indexed "equals_constant" 1) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 1),
    byteWordsize (name := .indexed "equals_constant" 2) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 2),
    selectHalfData (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design (.vector 32 .bit),
    selectByteData (name := .indexed "mux" 2) :=
      Silean.Modules.Mux.design (.vector 32 .bit),
    lowAddress (name := .indexed "vector_slice" 0) :=
      Silean.Modules.VectorSlice.design .bit 0 2 30,
    highHalfBit (name := .indexed "vector_slice" 1) :=
      Silean.Modules.VectorSlice.design .bit 1 1 30,
    highHalf (name := .indexed "equals_constant" 3) :=
      Silean.Modules.EqualsConstant.design (.vector 1 .bit) (fun _ => true),
    lowHalfMask (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design (.vector 4 .bit) (maskOfNat 0x3),
    highHalfMask (name := .indexed "constant" 1) :=
      Silean.Modules.Constant.design (.vector 4 .bit) (maskOfNat 0xc),
    halfMask (name := .indexed "mux" 3) :=
      Silean.Modules.Mux.design (.vector 4 .bit),
    byteMask (name := .indexed "binary_to_one_hot" 0) :=
      Silean.Modules.BinaryToOneHot.design 2,
    wordMask (name := .indexed "constant" 2) :=
      Silean.Modules.Constant.design (.vector 4 .bit) (maskOfNat 0xf),
    selectHalfMask (name := .indexed "mux" 4) :=
      Silean.Modules.Mux.design (.vector 4 .bit),
    selectByteMask (name := .indexed "mux" 5) :=
      Silean.Modules.Mux.design (.vector 4 .bit) }
  wiring {
  outputs {
    .mem_la_read := read.output,
    .mem_la_write := write.output,
    .mem_la_addr := address.result,
    .mem_la_wdata := selectByteData.result,
    .mem_la_wstrb := selectByteMask.result }
  instance (.currentFields) { .value := input.current }
  instance (.idle) { .value := currentFields[.mem_state] }
  instance (.enabledIdle) {
    .left := input.resetn,
    .right := idle.result }
  instance (.instructionCommand) {
    .left := input.mem_do_prefetch,
    .right := input.mem_do_rinst }
  instance (.readCommand) {
    .left := instructionCommand.output,
    .right := input.mem_do_rdata }
  instance (.read) {
    .left := enabledIdle.output,
    .right := readCommand.output }
  instance (.write) {
    .left := enabledIdle.output,
    .right := input.mem_do_wdata }
  instance (.alignedNextPc) { .input := input.next_pc }
  instance (.alignedRegOp1) { .input := input.reg_op1 }
  instance (.address) {
    .select := instructionCommand.output,
    .whenFalse := alignedRegOp1.output,
    .whenTrue := alignedNextPc.output }
  instance (.halfData) { .input := input.reg_op2 }
  instance (.byteData) { .input := input.reg_op2 }
  instance (.halfWordsize) { .value := input.mem_wordsize }
  instance (.byteWordsize) { .value := input.mem_wordsize }
  instance (.selectHalfData) {
    .select := halfWordsize.result,
    .whenFalse := input.reg_op2,
    .whenTrue := halfData.output }
  instance (.selectByteData) {
    .select := byteWordsize.result,
    .whenFalse := selectHalfData.result,
    .whenTrue := byteData.output }
  instance (.lowAddress) { .value := input.reg_op1 }
  instance (.highHalfBit) { .value := input.reg_op1 }
  instance (.highHalf) { .value := highHalfBit.result }
  instance (.lowHalfMask) {}
  instance (.highHalfMask) {}
  instance (.halfMask) {
    .select := highHalf.result,
    .whenFalse := lowHalfMask.output,
    .whenTrue := highHalfMask.output }
  instance (.byteMask) { .value := lowAddress.result }
  instance (.wordMask) {}
  instance (.selectHalfMask) {
    .select := halfWordsize.result,
    .whenFalse := wordMask.output,
    .whenTrue := halfMask.result }
  instance (.selectByteMask) {
    .select := byteWordsize.result,
    .whenFalse := selectHalfMask.result,
    .whenTrue := byteMask.result }
  }

end PicoRV.Memory
