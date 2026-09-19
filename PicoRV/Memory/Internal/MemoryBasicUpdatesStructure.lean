import PicoRV.Memory.MemoryNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Memory

open Silean
open Silean.Authoring

module_design ResponseCapture (name := "picorv32_memory_response_capture") where
  boundary (ResponseCapture.ports) (naming := ResponseCapture.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    transfer (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    response (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 32 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.transfer) {
    .left := currentFields[.mem_valid],
    .right := inputsFields[.mem_ready] }
  instance (.response) {
    .select := transfer.output,
    .whenFalse := currentFields[.mem_rdata_q],
    .whenTrue := inputsFields[.mem_rdata] }
  instance (.result) {
    .mem_state := currentFields[.mem_state],
    .mem_valid := currentFields[.mem_valid],
    .mem_instr := currentFields[.mem_instr],
    .mem_addr := currentFields[.mem_addr],
    .mem_wdata := currentFields[.mem_wdata],
    .mem_wstrb := currentFields[.mem_wstrb],
    .mem_rdata_q := response.result }
  }

module_design PhaseDecode (name := "picorv32_memory_phase_decode") where
  boundary (PhaseDecode.ports) (naming := PhaseDecode.Naming.ports)
  instances {
    idleMatch (name := .indexed "equals_constant" 0) := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 0),
    readMatch (name := .indexed "equals_constant" 1) := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 1),
    writeMatch (name := .indexed "equals_constant" 2) := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 2),
    prefetchedMatch (name := .indexed "equals_constant" 3) := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 3) }
  wiring {
  outputs {
    .idle := idleMatch.result,
    .read := readMatch.result,
    .write := writeMatch.result,
    .prefetched := prefetchedMatch.result }
  instance (.idleMatch) { .value := input.mem_state }
  instance (.readMatch) { .value := input.mem_state }
  instance (.writeMatch) { .value := input.mem_state }
  instance (.prefetchedMatch) { .value := input.mem_state }
  }

module_design IdleUpdate (name := "picorv32_memory_idle_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    instructionCommand (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    readCommand (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    trueBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit true,
    falseBit (name := .indexed "constant" 1) := Silean.Modules.Constant.design .bit false,
    zeroMask (name := .indexed "constant" 2) := Silean.Modules.Constant.design (.vector 4 .bit) (maskOfNat 0),
    readState (name := .indexed "constant" 3) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 1),
    writeState (name := .indexed "constant" 4) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 2),
    readValid (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    readInstr (name := .indexed "bit_mux" 1) := Silean.Modules.BitMux.design,
    readMask (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 4 .bit),
    readPhase (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 2 .bit),
    finalValid (name := .indexed "bit_mux" 2) := Silean.Modules.BitMux.design,
    finalInstr (name := .indexed "bit_mux" 3) := Silean.Modules.BitMux.design,
    finalPhase (name := .indexed "mux" 2) := Silean.Modules.Mux.design (.vector 2 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.instructionCommand) {
    .left := inputsFields[.mem_do_prefetch],
    .right := inputsFields[.mem_do_rinst] }
  instance (.readCommand) {
    .left := instructionCommand.output,
    .right := inputsFields[.mem_do_rdata] }
  instance (.trueBit) {}
  instance (.falseBit) {}
  instance (.zeroMask) {}
  instance (.readState) {}
  instance (.writeState) {}
  instance (.readValid) {
    .select := readCommand.output,
    .whenFalse := updatedFields[.mem_valid],
    .whenTrue := trueBit.output }
  instance (.readInstr) {
    .select := readCommand.output,
    .whenFalse := updatedFields[.mem_instr],
    .whenTrue := instructionCommand.output }
  instance (.readMask) {
    .select := readCommand.output,
    .whenFalse := updatedFields[.mem_wstrb],
    .whenTrue := zeroMask.output }
  instance (.readPhase) {
    .select := readCommand.output,
    .whenFalse := updatedFields[.mem_state],
    .whenTrue := readState.output }
  instance (.finalValid) {
    .select := inputsFields[.mem_do_wdata],
    .whenFalse := readValid.result,
    .whenTrue := trueBit.output }
  instance (.finalInstr) {
    .select := inputsFields[.mem_do_wdata],
    .whenFalse := readInstr.result,
    .whenTrue := falseBit.output }
  instance (.finalPhase) {
    .select := inputsFields[.mem_do_wdata],
    .whenFalse := readPhase.result,
    .whenTrue := writeState.output }
  instance (.result) {
    .mem_state := finalPhase.result,
    .mem_valid := finalValid.result,
    .mem_instr := finalInstr.result,
    .mem_addr := updatedFields[.mem_addr],
    .mem_wdata := updatedFields[.mem_wdata],
    .mem_wstrb := readMask.result,
    .mem_rdata_q := updatedFields[.mem_rdata_q] }
  }

module_design ReadUpdate (name := "picorv32_memory_read_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    transfer (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    activeRead (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    idleState (name := .indexed "constant" 1) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 0),
    prefetchedState (name := .indexed "constant" 2) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 3),
    completedPhase (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 2 .bit),
    valid (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    phase (name := .indexed "mux" 1) := Silean.Modules.Mux.design (.vector 2 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.transfer) {
    .left := currentFields[.mem_valid],
    .right := inputsFields[.mem_ready] }
  instance (.activeRead) {
    .left := inputsFields[.mem_do_rinst],
    .right := inputsFields[.mem_do_rdata] }
  instance (.falseBit) {}
  instance (.idleState) {}
  instance (.prefetchedState) {}
  instance (.completedPhase) {
    .select := activeRead.output,
    .whenFalse := prefetchedState.output,
    .whenTrue := idleState.output }
  instance (.valid) {
    .select := transfer.output,
    .whenFalse := updatedFields[.mem_valid],
    .whenTrue := falseBit.output }
  instance (.phase) {
    .select := transfer.output,
    .whenFalse := updatedFields[.mem_state],
    .whenTrue := completedPhase.result }
  instance (.result) {
    .mem_state := phase.result,
    .mem_valid := valid.result,
    .mem_instr := updatedFields[.mem_instr],
    .mem_addr := updatedFields[.mem_addr],
    .mem_wdata := updatedFields[.mem_wdata],
    .mem_wstrb := updatedFields[.mem_wstrb],
    .mem_rdata_q := updatedFields[.mem_rdata_q] }
  }

module_design WriteUpdate (name := "picorv32_memory_write_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    transfer (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    idleState (name := .indexed "constant" 1) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 0),
    valid (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    phase (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 2 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.transfer) {
    .left := currentFields[.mem_valid],
    .right := inputsFields[.mem_ready] }
  instance (.falseBit) {}
  instance (.idleState) {}
  instance (.valid) {
    .select := transfer.output,
    .whenFalse := updatedFields[.mem_valid],
    .whenTrue := falseBit.output }
  instance (.phase) {
    .select := transfer.output,
    .whenFalse := updatedFields[.mem_state],
    .whenTrue := idleState.output }
  instance (.result) {
    .mem_state := phase.result,
    .mem_valid := valid.result,
    .mem_instr := updatedFields[.mem_instr],
    .mem_addr := updatedFields[.mem_addr],
    .mem_wdata := updatedFields[.mem_wdata],
    .mem_wstrb := updatedFields[.mem_wstrb],
    .mem_rdata_q := updatedFields[.mem_rdata_q] }
  }

module_design PrefetchedUpdate (name := "picorv32_memory_prefetched_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    idleState (name := .indexed "constant" 0) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 0),
    phase (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 2 .bit),
    result (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.idleState) {}
  instance (.phase) {
    .select := inputsFields[.mem_do_rinst],
    .whenFalse := updatedFields[.mem_state],
    .whenTrue := idleState.output }
  instance (.result) {
    .mem_state := phase.result,
    .mem_valid := updatedFields[.mem_valid],
    .mem_instr := updatedFields[.mem_instr],
    .mem_addr := updatedFields[.mem_addr],
    .mem_wdata := updatedFields[.mem_wdata],
    .mem_wstrb := updatedFields[.mem_wstrb],
    .mem_rdata_q := updatedFields[.mem_rdata_q] }
  }

module_design ResetTrapOverride (name := "picorv32_memory_reset_trap_override") where
  boundary (ResetTrapOverride.ports) (naming := ResetTrapOverride.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    capturedFields (name := .indexed "named_tuple_splitter" 1) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    notResetn (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    resetOrTrap (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    clearValid (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    falseBit (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    idleState (name := .indexed "constant" 1) := Silean.Modules.Constant.design (.vector 2 .bit) (stateOfNat 0),
    overridePhase (name := .indexed "mux" 0) := Silean.Modules.Mux.design (.vector 2 .bit),
    overrideValid (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    overrideValue (name := .indexed "named_tuple_combiner" 0) := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema,
    selected (name := .indexed "mux" 1) := Silean.Modules.Mux.design stateType }
  wiring {
  outputs { .state := selected.result }
  instance (.inputsFields) { .value := input.inputs }
  instance (.capturedFields) { .value := input.captured }
  instance (.notResetn) { .input := inputsFields[.resetn] }
  instance (.resetOrTrap) {
    .left := notResetn.output,
    .right := inputsFields[.trap] }
  instance (.clearValid) {
    .left := notResetn.output,
    .right := inputsFields[.mem_ready] }
  instance (.falseBit) {}
  instance (.idleState) {}
  instance (.overridePhase) {
    .select := inputsFields[.resetn],
    .whenFalse := idleState.output,
    .whenTrue := capturedFields[.mem_state] }
  instance (.overrideValid) {
    .select := clearValid.output,
    .whenFalse := capturedFields[.mem_valid],
    .whenTrue := falseBit.output }
  instance (.overrideValue) {
    .mem_state := overridePhase.result,
    .mem_valid := overrideValid.result,
    .mem_instr := capturedFields[.mem_instr],
    .mem_addr := capturedFields[.mem_addr],
    .mem_wdata := capturedFields[.mem_wdata],
    .mem_wstrb := capturedFields[.mem_wstrb],
    .mem_rdata_q := capturedFields[.mem_rdata_q] }
  instance (.selected) {
    .select := resetOrTrap.output,
    .whenFalse := input.normal,
    .whenTrue := overrideValue.value }
  }

end PicoRV.Memory
