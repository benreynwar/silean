import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorReindex.VectorReindex
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorReindex.Internal

open Silean

private def indexCode (index : Fin inputWidth) : String :=
  s!"i{index.val}"

def variant (layout : Fin outputWidth → Fin inputWidth) : String :=
  String.intercalate "_" <|
    (List.finRange outputWidth).map fun index => indexCode (layout index)

def splitter (element : SignalType) (inputWidth : Nat) :
    Composition.SignalSplitter :=
  .vector inputWidth element

def combiner (element : SignalType) (outputWidth : Nat) :
    Composition.SignalCombiner :=
  .vector outputWidth element

end Silean.Modules.VectorReindex.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorReindex (element : SignalType) (inputWidth : Nat)
    (outputWidth : Nat)
    (layout : Fin outputWidth → Fin inputWidth)
    (variant := VectorReindex.Internal.variant layout)
    (specialization :=
      [.signalType element, .natural inputWidth, .natural outputWidth])
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  boundary (VectorReindex.ports element inputWidth outputWidth)
    (naming := VectorReindex.Naming.ports element inputWidth outputWidth)
    (namingWith := VectorReindex.Naming.portsWithNaming
      element inputWidth outputWidth elementNaming)
  instances {
    split
      (naming := Naming.SignalAdapter.splitterWithNaming
        (.vector inputWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.splitterDesign
        (VectorReindex.Internal.splitter element inputWidth),
    combine
      (naming := Naming.SignalAdapter.combinerWithNaming
        (.vector outputWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.combinerDesign
        (VectorReindex.Internal.combiner element outputWidth) }
  wiring {
    outputs {
      .output := combine.value }
    instance (.split) {
      .value := input.input }
    instance (.combine) {
      index := split[layout index] }
  }

end Silean.Modules
