import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorConcat.Internal

open Silean

def leftSplitter (element : SignalType) (leftWidth : Nat) :
    Composition.SignalSplitter :=
  .vector leftWidth element

def rightSplitter (element : SignalType) (rightWidth : Nat) :
    Composition.SignalSplitter :=
  .vector rightWidth element

def combiner (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalCombiner :=
  .vector (leftWidth + rightWidth) element

end Silean.Modules.VectorConcat.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorConcat (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  boundary (VectorConcat.ports element leftWidth rightWidth)
    (naming := VectorConcat.Naming.ports element leftWidth rightWidth)
    (namingWith := VectorConcat.Naming.portsWithNaming
      element leftWidth rightWidth elementNaming)
  instances {
    leftSplit
      (naming := Naming.SignalAdapter.splitterWithNaming
        (.vector leftWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.splitterDesign
        (VectorConcat.Internal.leftSplitter element leftWidth),
    rightSplit
      (naming := Naming.SignalAdapter.splitterWithNaming
        (.vector rightWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.splitterDesign
        (VectorConcat.Internal.rightSplitter element rightWidth),
    combine
      (naming := Naming.SignalAdapter.combinerWithNaming
        (.vector (leftWidth + rightWidth) element) (.vector elementNaming)) :=
      Naming.SignalAdapter.combinerDesign
        (VectorConcat.Internal.combiner element leftWidth rightWidth) }
  wiring {
    outputs {
      .result := combine.value }
    instance (.leftSplit) {
      .value := input.left }
    instance (.rightSplit) {
      .value := input.right }
    instance (.combine) {
      index := from (Fin.addCases
        (fun leftIndex =>
          (VectorConcat.context element leftWidth rightWidth).instanceOutput
            .leftSplit leftIndex)
        (fun rightIndex =>
          (VectorConcat.context element leftWidth rightWidth).instanceOutput
            .rightSplit rightIndex)
        index) }
  }

end Silean.Modules
