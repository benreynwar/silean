import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSplit.VectorSplit
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorSplit.Internal

open Silean

def splitter (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalSplitter :=
  .vector (leftWidth + rightWidth) element

def leftCombiner (element : SignalType) (leftWidth : Nat) :
    Composition.SignalCombiner :=
  .vector leftWidth element

def rightCombiner (element : SignalType) (rightWidth : Nat) :
    Composition.SignalCombiner :=
  .vector rightWidth element

end Silean.Modules.VectorSplit.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorSplit (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  boundary (VectorSplit.ports element leftWidth rightWidth)
    (naming := VectorSplit.Naming.ports element leftWidth rightWidth)
    (namingWith := VectorSplit.Naming.portsWithNaming
      element leftWidth rightWidth elementNaming)
  instances {
    split
      (naming := Naming.SignalAdapter.splitterWithNaming
        (.vector (leftWidth + rightWidth) element) (.vector elementNaming)) :=
      Naming.SignalAdapter.splitterDesign
        (VectorSplit.Internal.splitter element leftWidth rightWidth),
    left (name := "combineLeft")
      (naming := Naming.SignalAdapter.combinerWithNaming
        (.vector leftWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.combinerDesign
        (VectorSplit.Internal.leftCombiner element leftWidth),
    right (name := "combineRight")
      (naming := Naming.SignalAdapter.combinerWithNaming
        (.vector rightWidth element) (.vector elementNaming)) :=
      Naming.SignalAdapter.combinerDesign
        (VectorSplit.Internal.rightCombiner element rightWidth) }
  wiring {
    outputs {
      .left := left.value,
      .right := right.value }
    instance (.split) {
      .value := input.value }
    instance (.left) {
      index := from ((VectorSplit.context element leftWidth rightWidth).instanceOutput
        .split (Fin.castAdd rightWidth index)) }
    instance (.right) {
      index := from ((VectorSplit.context element leftWidth rightWidth).instanceOutput
        .split (Fin.natAdd leftWidth index)) }
  }

end Silean.Modules
