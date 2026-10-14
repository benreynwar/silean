import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.Equality.EqualityDerived
import Silean.Modules.Fifo.FifoPointerControl
import Silean.Primitives

namespace Silean.Modules.Fifo

open Silean
open Silean.Authoring

/-! Expanded typed structure for the reader-facing FIFO pointer controller. -/

module_design PointerControl (addressWidth : Nat) where
  boundary (PointerControl.ports addressWidth)
    (naming := PointerControl.Naming.ports addressWidth)
  instances {
    readSplit (name := .indexed "splitter" 0) := Naming.SignalAdapter.splitterDesign
      (PointerControl.pointerSplitter addressWidth),
    writeSplit (name := .indexed "splitter" 1) := Naming.SignalAdapter.splitterDesign
      (PointerControl.pointerSplitter addressWidth),
    readAddress (name := .indexed "combiner" 0) := Naming.SignalAdapter.combinerDesign
      (PointerControl.addressCombiner addressWidth),
    writeAddress (name := .indexed "combiner" 1) := Naming.SignalAdapter.combinerDesign
      (PointerControl.addressCombiner addressWidth),
    addressEquality (name := .indexed "equality" 0) := Equality.design
      (PointerControl.addressType addressWidth),
    wrapEquality (name := .indexed "eq" 0) := Primitives.eqDesign,
    wrapDifference (name := .indexed "not" 0) := Primitives.notDesign,
    fullGate (name := .indexed "and" 0) := Primitives.andDesign,
    readyInverter (name := .indexed "not" 1) := Primitives.notDesign,
    emptyGate (name := .indexed "and" 1) := Primitives.andDesign,
    validInverter (name := .indexed "not" 2) := Primitives.notDesign,
    readGate (name := .indexed "and" 2) := Primitives.andDesign,
    writeGate (name := .indexed "and" 3) := Primitives.andDesign }
  named_wires {
    addressesEqual := addressEquality.result,
    wrapsEqual := wrapEquality.output }
  wiring {
    outputs {
      .readAddress := readAddress.value,
      .writeAddress := writeAddress.value,
      .inputReady := readyInverter.output,
      .outputValid := validInverter.output,
      .readAdvance := readGate.output,
      .writeAdvance := writeGate.output }
    instance (.readSplit) { .value := input.readPointer }
    instance (.writeSplit) { .value := input.writePointer }
    instance (.readAddress) { index := readSplit[index.castSucc] }
    instance (.writeAddress) { index := writeSplit[index.castSucc] }
    instance (.addressEquality) {
      .left := readAddress.value,
      .right := writeAddress.value }
    instance (.wrapEquality) {
      .left := readSplit[Fin.last addressWidth],
      .right := writeSplit[Fin.last addressWidth] }
    instance (.wrapDifference) { .input := wrapEquality.output }
    instance (.emptyGate) {
      .left := addressEquality.result,
      .right := wrapEquality.output }
    instance (.fullGate) {
      .left := addressEquality.result,
      .right := wrapDifference.output }
    instance (.readyInverter) { .input := fullGate.output }
    instance (.validInverter) { .input := emptyGate.output }
    instance (.readGate) {
      .left := validInverter.output,
      .right := input.outputReady }
    instance (.writeGate) {
      .left := input.inputValid,
      .right := readyInverter.output }
  }

end Silean.Modules.Fifo
