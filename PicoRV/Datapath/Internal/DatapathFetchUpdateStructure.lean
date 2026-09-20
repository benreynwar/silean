import PicoRV.Datapath.DatapathNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.AddDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

def FetchUpdate.clearLowLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if _zero : index.val = 0 then .constant false else .input index

/-! Fetch commits the prospective PC, optionally selecting the aligned
registered branch target first. A current decoder trigger then computes the
following sequential or JAL PC from that same selected current PC. -/
module_design FetchUpdate (name := "picorv32_datapath_fetch_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    four (name := .indexed "constant" 1) := Silean.Modules.Constant.design (.vector 32 .bit) (wordOfNat 4),
    branchStored (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    branchSource (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 32 .bit),
    alignedBranch (name := .indexed "vector_layout" 0) := Silean.Modules.VectorLayout.design 32 32 FetchUpdate.clearLowLayout,
    currentPc (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 32 .bit),
    sequentialPc (name := .indexed "add" 0) := Silean.Modules.Add.design 32,
    jalPc (name := .indexed "add" 1) := Silean.Modules.Add.design 32,
    decodedPc (name := .indexed "mux" 2) := Silean.Modules.Mux.design (.vector 32 .bit),
    nextPc (name := .indexed "mux" 3) := Silean.Modules.Mux.design (.vector 32 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.four) {}
  instance (.branchStored) {
    .left := inputsFields[.latched_branch],
    .right := inputsFields[.latched_store] }
  instance (.branchSource) {
    .select := inputsFields[.latched_stalu],
    .whenFalse := currentFields[.reg_out],
    .whenTrue := currentFields[.alu_out_q] }
  instance (.alignedBranch) { .input := branchSource.result }
  instance (.currentPc) {
    .select := branchStored.output,
    .whenFalse := currentFields[.reg_next_pc],
    .whenTrue := alignedBranch.output }
  instance (.sequentialPc) {
    .left := currentPc.result, .right := four.output,
    .carryIn := falseBit.output }
  instance (.jalPc) {
    .left := currentPc.result, .right := inputsFields[.decoded_imm_j],
    .carryIn := falseBit.output }
  instance (.decodedPc) {
    .select := inputsFields[.instr_jal],
    .whenFalse := sequentialPc.result,
    .whenTrue := jalPc.result }
  instance (.nextPc) {
    .select := inputsFields[.decoder_trigger],
    .whenFalse := currentPc.result,
    .whenTrue := decodedPc.result }
  instance (.result) {
    .reg_pc := currentPc.result,
    .reg_next_pc := nextPc.result,
    .reg_op1 := updatedFields[.reg_op1],
    .reg_op2 := updatedFields[.reg_op2],
    .reg_out := updatedFields[.reg_out],
    .reg_sh := updatedFields[.reg_sh],
    .alu_out_q := updatedFields[.alu_out_q] }
  }

end PicoRV.Datapath
