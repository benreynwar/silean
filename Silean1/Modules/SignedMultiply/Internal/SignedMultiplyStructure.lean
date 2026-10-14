import Silean.Authoring.ModuleDesign
import Silean.Modules.SignedMultiply.SignedMultiply
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Expanded typed structure for the reader-facing signed multiplier. -/

module_design SignedMultiply (leftWidth : Nat) (rightWidth : Nat) where
  boundary (SignedMultiply.ports leftWidth rightWidth)
    (naming := SignedMultiply.Naming.ports leftWidth rightWidth)
  instances {
    leftSignLayout (name := .indexed "vector_layout" 0) :=
      VectorLayout.design leftWidth 1 (SignedMultiply.signLayout leftWidth),
    leftSignSplit (name := .indexed "splitter" 0) :=
      Silean.Naming.SignalAdapter.splitterDesign (.vector 1 .bit),
    rightSignLayout (name := .indexed "vector_layout" 1) :=
      VectorLayout.design rightWidth 1 (SignedMultiply.signLayout rightWidth),
    rightSignSplit (name := .indexed "splitter" 1) :=
      Silean.Naming.SignalAdapter.splitterDesign (.vector 1 .bit),
    leftMagnitude (name := .indexed "conditional_negate" 0) :=
      ConditionalNegate.design leftWidth,
    rightMagnitude (name := .indexed "conditional_negate" 1) :=
      ConditionalNegate.design rightWidth,
    productSign (name := .indexed "xor" 0) := Primitives.xorDesign,
    magnitudeProduct (name := .indexed "unsigned_multiply" 0) :=
      UnsignedMultiply.design leftWidth rightWidth,
    resultNegate (name := .indexed "conditional_negate" 2) :=
      ConditionalNegate.design (leftWidth + rightWidth) }
  named_wires {
    productNegate := productSign.output }
  wiring {
    outputs {
      .result := resultNegate.result }
    instance (.leftSignLayout) {
      .input := input.left }
    instance (.leftSignSplit) {
      .value := leftSignLayout.output }
    instance (.rightSignLayout) {
      .input := input.right }
    instance (.rightSignSplit) {
      .value := rightSignLayout.output }
    instance (.leftMagnitude) {
      .value := input.left,
      .negate := leftSignSplit[0] }
    instance (.rightMagnitude) {
      .value := input.right,
      .negate := rightSignSplit[0] }
    instance (.productSign) {
      .left := leftSignSplit[0],
      .right := rightSignSplit[0] }
    instance (.magnitudeProduct) {
      .left := leftMagnitude.result,
      .right := rightMagnitude.result }
    instance (.resultNegate) {
      .value := magnitudeProduct.result,
      .negate := productSign.output }
  }

end Silean.Modules
