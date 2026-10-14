import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorLayout.Internal

open Silean

private def sourceCode : BitSource inputWidth → String
  | .input index => s!"i{index.val}"
  | .constant false => "f"
  | .constant true => "t"

def variant (layout : Fin outputWidth → BitSource inputWidth) : String :=
  String.intercalate "_" <|
    (List.finRange outputWidth).map fun index => sourceCode (layout index)

def splitter (inputWidth : Nat) : Composition.SignalSplitter :=
  .vector inputWidth .bit

def combiner (outputWidth : Nat) : Composition.SignalCombiner :=
  .vector outputWidth .bit

end Silean.Modules.VectorLayout.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorLayout (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → VectorLayout.BitSource inputWidth)
    (variant := VectorLayout.Internal.variant layout)
    (specialization := [.natural inputWidth, .natural outputWidth]) where
  boundary (VectorLayout.ports inputWidth outputWidth)
    (naming := VectorLayout.Naming.ports inputWidth outputWidth)
  instances {
    split := Naming.SignalAdapter.splitterDesign
      (VectorLayout.Internal.splitter inputWidth),
    falseBit := Primitives.constantDesign false,
    trueBit := Primitives.constantDesign true,
    combine := Naming.SignalAdapter.combinerDesign
      (VectorLayout.Internal.combiner outputWidth) }
  wiring {
    outputs {
      .output := combine.value }
    instance (.split) {
      .value := input.input }
    instance (.falseBit) {}
    instance (.trueBit) {}
    instance (.combine) {
      index := from (if isInput : (layout index).IsInput then
          (context inputWidth outputWidth layout).instanceOutput .split
            ((layout index).inputIndex isInput)
        else if _isTrue : layout index = .constant true then
          (context inputWidth outputWidth layout).instanceOutput .trueBit .output
        else
          (context inputWidth outputWidth layout).instanceOutput .falseBit .output) }
  }

end Silean.Modules
