import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Misalignment is determined entirely by the current request, its word size,
and the low address bits. The structure intentionally exposes those low-bit
tests rather than implementing division or remainder hardware. -/

def Alignment.wordSplitter : Composition.SignalSplitter := .vector 32 .bit

module_design Alignment (name := "picorv32_control_alignment") where
  boundary (Alignment.ports) (naming := Alignment.Naming.ports)
  instances {
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    stateFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    op1Bits := Naming.SignalAdapter.splitterDesign Alignment.wordSplitter,
    pcBits := Naming.SignalAdapter.splitterDesign Alignment.wordSplitter,
    sizeIsWord := Modules.EqualsConstant.design (.vector 2 .bit)
      (twoBitsOfNat 0),
    sizeIsHalf := Modules.EqualsConstant.design (.vector 2 .bit)
      (twoBitsOfNat 1),
    dataCommand := Primitives.orDesign,
    op1Low := Primitives.orDesign,
    pcLow := Primitives.orDesign,
    wordMisaligned := Primitives.andDesign,
    halfMisaligned := Primitives.andDesign,
    sizeMisaligned := Primitives.orDesign,
    dataMisaligned := Primitives.andDesign,
    instructionMisaligned := Primitives.andDesign }
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

end Silean.Examples.PicoRV.Control
