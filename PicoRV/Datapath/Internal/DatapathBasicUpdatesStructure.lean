import PicoRV.Datapath.DatapathNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.Add
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

module_design PhaseDecode (name := "picorv32_datapath_phase_decode") where
  boundary (PhaseDecode.ports) (naming := PhaseDecode.Naming.ports)
  instances {
    fetchMatch (name := .indexed "equals_constant" 0) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    loadRs1Match (name := .indexed "equals_constant" 1) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs1),
    loadRs2Match (name := .indexed "equals_constant" 2) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs2),
    executeMatch (name := .indexed "equals_constant" 3) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateExec),
    shiftMatch (name := .indexed "equals_constant" 4) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateShift),
    storeMatch (name := .indexed "equals_constant" 5) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateStmem),
    loadMatch (name := .indexed "equals_constant" 6) := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdmem) }
  wiring {
  outputs {
    .fetch := fetchMatch.result,
    .loadRs1 := loadRs1Match.result,
    .loadRs2 := loadRs2Match.result,
    .execute := executeMatch.result,
    .shift := shiftMatch.result,
    .store := storeMatch.result,
    .load := loadMatch.result }
  instance (.fetchMatch) { .value := input.cpu_state }
  instance (.loadRs1Match) { .value := input.cpu_state }
  instance (.loadRs2Match) { .value := input.cpu_state }
  instance (.executeMatch) { .value := input.cpu_state }
  instance (.shiftMatch) { .value := input.cpu_state }
  instance (.storeMatch) { .value := input.cpu_state }
  instance (.loadMatch) { .value := input.cpu_state }
  }

module_design Baseline (name := "picorv32_datapath_baseline") where
  boundary (Baseline.ports) (naming := Baseline.Naming.ports)
  instances {
    currentFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.currentFields) { .value := input.current }
  instance (.result) {
    .reg_pc := currentFields[.reg_pc],
    .reg_next_pc := currentFields[.reg_next_pc],
    .reg_op1 := currentFields[.reg_op1],
    .reg_op2 := currentFields[.reg_op2],
    .reg_out := currentFields[.reg_out],
    .reg_sh := currentFields[.reg_sh],
    .alu_out_q := input.alu_out }
  }

def LoadRs2Update.lowFiveLayout (index : Fin 5) :
    Silean.Modules.VectorLayout.BitSource 32 := .input ⟨index.val, by omega⟩

module_design LoadRs2Update (name := "picorv32_datapath_load_rs2_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    lowFive (name := .indexed "vector_layout" 0) := Silean.Modules.VectorLayout.design 32 5 LoadRs2Update.lowFiveLayout,
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.lowFive) { .input := inputsFields[.cpuregs_rs2] }
  instance (.result) {
    .reg_pc := updatedFields[.reg_pc],
    .reg_next_pc := updatedFields[.reg_next_pc],
    .reg_op1 := updatedFields[.reg_op1],
    .reg_op2 := inputsFields[.cpuregs_rs2],
    .reg_out := updatedFields[.reg_out],
    .reg_sh := lowFive.output,
    .alu_out_q := updatedFields[.alu_out_q] }
  }

module_design ExecuteUpdate (name := "picorv32_datapath_execute_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    target (name := .indexed "add" 0) := Silean.Modules.Add.design 32,
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.target) {
    .left := currentFields[.reg_pc],
    .right := inputsFields[.decoded_imm],
    .carryIn := falseBit.output }
  instance (.result) {
    .reg_pc := updatedFields[.reg_pc],
    .reg_next_pc := updatedFields[.reg_next_pc],
    .reg_op1 := updatedFields[.reg_op1],
    .reg_op2 := updatedFields[.reg_op2],
    .reg_out := target.result,
    .reg_sh := updatedFields[.reg_sh],
    .alu_out_q := updatedFields[.alu_out_q] }
  }

module_design ResetOverride (name := "picorv32_datapath_reset_override") where
  boundary (ResetOverride.ports) (naming := ResetOverride.Naming.ports)
  instances {
    selectedFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    zeroWord (name := .indexed "constant" 0) := Silean.Modules.Constant.design (.vector 32 .bit) (wordOfNat 0),
    pc (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 32 .bit),
    nextPc (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 32 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.selectedFields) { .value := input.selected }
  instance (.zeroWord) {}
  instance (.pc) {
    .select := input.resetn,
    .whenFalse := zeroWord.output,
    .whenTrue := selectedFields[.reg_pc] }
  instance (.nextPc) {
    .select := input.resetn,
    .whenFalse := zeroWord.output,
    .whenTrue := selectedFields[.reg_next_pc] }
  instance (.result) {
    .reg_pc := pc.result,
    .reg_next_pc := nextPc.result,
    .reg_op1 := selectedFields[.reg_op1],
    .reg_op2 := selectedFields[.reg_op2],
    .reg_out := selectedFields[.reg_out],
    .reg_sh := selectedFields[.reg_sh],
    .alu_out_q := selectedFields[.alu_out_q] }
  }

end PicoRV.Datapath
