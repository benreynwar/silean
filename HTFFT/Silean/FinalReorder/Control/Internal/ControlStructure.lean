import HTFFT.Silean.FinalReorder.Control.Control
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Constant.Constant
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Equality.EqualityDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace HTFFT.Silean.FinalReorder.Control.Internal

open _root_.Silean

@[reducible] def addressSplitter (addressWidth : Nat) : Composition.SignalSplitter :=
  .vector addressWidth .bit

@[reducible] def addressCombiner (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector addressWidth .bit

@[reducible] def oneBitSplitter : Composition.SignalSplitter :=
  .vector 1 .bit

def lowBitLayout : (addressWidth : Nat) →
    Fin 1 → Modules.VectorLayout.BitSource addressWidth
  | 0, _ => .constant false
  | _ + 1, _ => .input 0

def highBitLayout : (addressWidth : Nat) →
    Fin 1 → Modules.VectorLayout.BitSource addressWidth
  | 0, _ => .constant false
  | width + 1, _ => .input (Fin.last width)

end HTFFT.Silean.FinalReorder.Control.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FinalReorder.Control (addressWidth : Nat) where
  boundary (FinalReorder.Control.ports addressWidth)
    (naming := FinalReorder.Control.Naming.ports addressWidth)
  instances {
    trueSource := Constant.design .bit true,
    zeroAddress := Constant.design (.vector addressWidth .bit)
      (FinalReorder.Control.zeroAddress addressWidth),
    lastAddress := Constant.design (.vector addressWidth .bit)
      (FinalReorder.Control.lastAddress addressWidth),
    writeCounter := EnabledResetCounter.design addressWidth
      (FinalReorder.Control.oneAddress addressWidth),
    readCounter := EnabledResetCounter.design addressWidth
      (FinalReorder.Control.oneAddress addressWidth),
    writeSelect := Mux.design (.vector addressWidth .bit),
    readSelect := Mux.design (.vector addressWidth .bit),
    writeSplit := Naming.SignalAdapter.splitterDesign
      (FinalReorder.Control.Internal.addressSplitter addressWidth),
    lowSelect := VectorLayout.design addressWidth 1
      (FinalReorder.Control.Internal.lowBitLayout addressWidth),
    lowSplit := Naming.SignalAdapter.splitterDesign
      FinalReorder.Control.Internal.oneBitSplitter,
    highSelect := VectorLayout.design addressWidth 1
      (FinalReorder.Control.Internal.highBitLayout addressWidth),
    highSplit := Naming.SignalAdapter.splitterDesign
      FinalReorder.Control.Internal.oneBitSplitter,
    lowInvert := Primitives.notDesign,
    writeAddress0 := Naming.SignalAdapter.combinerDesign
      (FinalReorder.Control.Internal.addressCombiner addressWidth),
    writeAddress1 := Naming.SignalAdapter.combinerDesign
      (FinalReorder.Control.Internal.addressCombiner addressWidth),
    bypass := Equality.design (.vector addressWidth .bit) }
  wiring {
    outputs {
      .o_writeAddress0 := writeAddress0.value,
      .o_writeAddress1 := writeAddress1.value,
      .o_readAddress := readSelect.result,
      .o_writeSwap := lowSplit[0],
      .o_readSwap := highSplit[0],
      .o_bypass := bypass.result }
    instance (.trueSource) {}
    instance (.zeroAddress) {}
    instance (.lastAddress) {}
    instance (.writeCounter) {
      .enable := trueSource.output,
      .reset := input.i_first }
    instance (.readCounter) {
      .enable := trueSource.output,
      .reset := input.i_readFirst }
    instance (.writeSelect) {
      .select := input.i_first,
      .whenFalse := writeCounter.value,
      .whenTrue := zeroAddress.output }
    instance (.readSelect) {
      .select := input.i_readFirst,
      .whenFalse := readCounter.value,
      .whenTrue := zeroAddress.output }
    instance (.writeSplit) {
      .value := writeSelect.result }
    instance (.lowSelect) {
      .input := writeSelect.result }
    instance (.lowSplit) {
      .value := lowSelect.output }
    instance (.highSelect) {
      .input := readSelect.result }
    instance (.highSplit) {
      .value := highSelect.output }
    instance (.lowInvert) {
      .input := lowSplit[0] }
    instance (.writeAddress0) {
      index := from (if nextInRange : index.val + 1 < addressWidth then
        (context addressWidth).instanceOutput
          .writeSplit ⟨index.val + 1, nextInRange⟩
      else
        (context addressWidth).instanceOutput
          .writeSplit ⟨0, Nat.zero_lt_of_lt index.isLt⟩) }
    instance (.writeAddress1) {
      index := from (if nextInRange : index.val + 1 < addressWidth then
        (context addressWidth).instanceOutput
          .writeSplit ⟨index.val + 1, nextInRange⟩
      else
        (context addressWidth).instanceOutput
          .lowInvert .output) }
    instance (.bypass) {
      .left := writeSelect.result,
      .right := lastAddress.output }
  }

end HTFFT.Silean
