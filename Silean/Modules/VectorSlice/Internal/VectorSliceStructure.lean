import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorSlice.Internal

open Silean

def splitter (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    Composition.SignalSplitter :=
  .vector (prefixWidth + width + suffixWidth) element

def combiner (element : SignalType) (width : Nat) :
    Composition.SignalCombiner :=
  .vector width element

end Silean.Modules.VectorSlice.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorSlice (element : SignalType) (prefixWidth : Nat)
    (width : Nat) (suffixWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  boundary (VectorSlice.ports element prefixWidth width suffixWidth)
    (naming := VectorSlice.Naming.ports element prefixWidth width suffixWidth)
    (namingWith := VectorSlice.Naming.portsWithNaming
      element prefixWidth width suffixWidth elementNaming)
  instances {
    split
      (naming := Naming.SignalAdapter.splitterWithNaming
        (.vector (prefixWidth + width + suffixWidth) element)
        (.vector elementNaming)) :=
      Naming.SignalAdapter.splitterDesign
        (VectorSlice.Internal.splitter element prefixWidth width suffixWidth),
    combine
      (naming := Naming.SignalAdapter.combinerWithNaming
        (.vector width element) (.vector elementNaming)) :=
      Naming.SignalAdapter.combinerDesign
        (VectorSlice.Internal.combiner element width) }
  wiring {
    outputs {
      .result := combine.value }
    instance (.split) {
      .value := input.value }
    instance (.combine) {
      index := from ((VectorSlice.context element prefixWidth width suffixWidth).instanceOutput
        .split (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index))) }
  }

end Silean.Modules
