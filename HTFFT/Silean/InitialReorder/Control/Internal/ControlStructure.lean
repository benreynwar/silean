import HTFFT.Silean.InitialReorder.Control.Control
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Constant.Constant
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Equality.EqualityDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Naming.SignalAdapterNaming

namespace HTFFT.Silean.InitialReorder.Control.Internal

open _root_.Silean

def orientationValue (value : Bool) : Fin 1 → Bool := fun _ => value

@[reducible] def orientationSplitter : Composition.SignalSplitter :=
  .vector 1 .bit

end HTFFT.Silean.InitialReorder.Control.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design InitialReorder.Control (addressWidth : Nat) where
  boundary (InitialReorder.Control.ports addressWidth)
    (naming := InitialReorder.Control.Naming.ports addressWidth)
  instances {
    trueSource := Constant.design .bit true,
    falseSource := Constant.design .bit false,
    zeroAddress := Constant.design (.vector addressWidth .bit)
      (InitialReorder.Control.zeroAddress addressWidth),
    lastAddress := Constant.design (.vector addressWidth .bit)
      (InitialReorder.Control.lastAddress addressWidth),
    addressCounter := EnabledResetCounter.design addressWidth
      (InitialReorder.Control.oneAddress addressWidth),
    addressSelect := Mux.design (.vector addressWidth .bit),
    atLast := Equality.design (.vector addressWidth .bit),
    orientationCounter := EnabledResetCounter.design 1
      (InitialReorder.Control.Internal.orientationValue false),
    orientationSplit := Naming.SignalAdapter.splitterDesign
      InitialReorder.Control.Internal.orientationSplitter }
  wiring {
    outputs {
      .o_address := addressSelect.result,
      .o_reversed := orientationSplit[0] }
    instance (.trueSource) {}
    instance (.falseSource) {}
    instance (.zeroAddress) {}
    instance (.lastAddress) {}
    instance (.addressCounter) {
      .enable := trueSource.output,
      .reset := input.i_first }
    instance (.addressSelect) {
      .select := input.i_first,
      .whenFalse := addressCounter.value,
      .whenTrue := zeroAddress.output }
    instance (.atLast) {
      .left := addressSelect.result,
      .right := lastAddress.output }
    instance (.orientationCounter) {
      .enable := atLast.result,
      .reset := falseSource.output }
    instance (.orientationSplit) {
      .value := orientationCounter.value }
  }

end HTFFT.Silean
