import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

def Alignment.wordSplitter : Silean.Composition.SignalSplitter := .vector 32 .bit

/-! Expanded typed production structure corresponding to the concise authored
definition in `ControlAlignment.lean`. -/

module_design Alignment (name := "picorv32_control_alignment") where
  boundary (Alignment.ports) (naming := Alignment.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    stateFields (name := .indexed "named_tuple_splitter" 1) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    op1Bits (name := .indexed "vector_splitter" 0) :=
      Naming.SignalAdapter.splitterDesign Alignment.wordSplitter,
    pcBits (name := .indexed "vector_splitter" 1) :=
      Naming.SignalAdapter.splitterDesign Alignment.wordSplitter,
    sizeIsWord (name := .indexed "equals_constant" 0) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (twoBitsOfNat 0),
    sizeIsHalf (name := .indexed "equals_constant" 1) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (twoBitsOfNat 1),
    dataCommand (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    op1Low (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    pcLow (name := .indexed "or" 2) := Silean.Primitives.orDesign,
    wordMisaligned (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    halfMisaligned (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    sizeMisaligned (name := .indexed "or" 3) := Silean.Primitives.orDesign,
    dataMisaligned (name := .indexed "and" 2) := Silean.Primitives.andDesign,
    instructionMisaligned (name := .indexed "and" 3) :=
      Silean.Primitives.andDesign }
  wiring {
  outputs {
    .data := dataMisaligned.output,
    .instruction := instructionMisaligned.output }
  instance (.inputsFields) { .value := input.inputs }
  instance (.stateFields) { .value := input.current }
  instance (.op1Bits) { .value := inputsFields[.reg_op1] }
  instance (.pcBits) { .value := inputsFields[.reg_pc] }
  instance (.sizeIsWord) { .value := stateFields[.mem_wordsize] }
  instance (.sizeIsHalf) { .value := stateFields[.mem_wordsize] }
  instance (.dataCommand) {
    .left := stateFields[.mem_do_rdata],
    .right := stateFields[.mem_do_wdata] }
  instance (.op1Low) {
    .left := op1Bits[(0 : Fin 32)], .right := op1Bits[(1 : Fin 32)] }
  instance (.pcLow) {
    .left := pcBits[(0 : Fin 32)], .right := pcBits[(1 : Fin 32)] }
  instance (.wordMisaligned) {
    .left := sizeIsWord.result,
    .right := op1Low.output }
  instance (.halfMisaligned) {
    .left := sizeIsHalf.result,
    .right := op1Bits[(0 : Fin 32)] }
  instance (.sizeMisaligned) {
    .left := wordMisaligned.output,
    .right := halfMisaligned.output }
  instance (.dataMisaligned) {
    .left := dataCommand.output,
    .right := sizeMisaligned.output }
  instance (.instructionMisaligned) {
    .left := stateFields[.mem_do_rinst],
    .right := pcLow.output }
  }

end PicoRV.Control
