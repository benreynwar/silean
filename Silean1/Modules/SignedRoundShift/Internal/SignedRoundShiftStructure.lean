import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Any.Any
import Silean.Modules.Increment.IncrementDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.SignedRoundShift.Internal.SignedRoundShiftArithmetic
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Modules.VectorSlice.VectorSliceDerived
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.AndPrimitive
import Silean.Primitives.OrPrimitive

namespace Silean.Modules.SignedRoundShift.Internal

open Silean

def splitter (width : Nat) : Composition.SignalSplitter :=
  .vector width .bit

def firstBit : (splitter 1).ports.outputs.Label :=
  ⟨0, by omega⟩

end Silean.Modules.SignedRoundShift.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Structural signed rounded shift: fixed wiring selects the retained,
guard, sticky, and parity bits; an incrementer and mux perform rounding. -/

module_design SignedRoundShift (retainedWidth : Nat) (discardedWidth : Nat) where
  boundary (SignedRoundShift.ports retainedWidth discardedWidth)
    (naming := SignedRoundShift.Naming.ports retainedWidth discardedWidth)
  instances {
    retained (name := .indexed "vector_slice" 0) :=
      VectorSlice.design .bit discardedWidth retainedWidth 0,
    guardLayout (name := .indexed "vector_layout" 0) :=
      VectorLayout.design (discardedWidth + retainedWidth) 1
        (SignedRoundShift.Internal.guardLayout retainedWidth discardedWidth),
    guardSplit (name := .indexed "splitter" 0) :=
      Naming.SignalAdapter.splitterDesign
        (SignedRoundShift.Internal.splitter 1),
    stickyLayout (name := .indexed "vector_layout" 1) :=
      VectorLayout.design (discardedWidth + retainedWidth) discardedWidth
        (SignedRoundShift.Internal.stickyLayout retainedWidth discardedWidth),
    stickySplit (name := .indexed "splitter" 1) :=
      Naming.SignalAdapter.splitterDesign
        (SignedRoundShift.Internal.splitter discardedWidth),
    stickyAny (name := .indexed "any" 0) := Any.design discardedWidth,
    retainedLsbLayout (name := .indexed "vector_layout" 2) :=
      VectorLayout.design (discardedWidth + retainedWidth) 1
        (SignedRoundShift.Internal.retainedLsbLayout
          retainedWidth discardedWidth),
    retainedLsbSplit (name := .indexed "splitter" 2) :=
      Naming.SignalAdapter.splitterDesign
        (SignedRoundShift.Internal.splitter 1),
    roundOr (name := .indexed "or" 0) := Primitives.orDesign,
    roundAnd (name := .indexed "and" 0) := Primitives.andDesign,
    increment (name := .indexed "increment" 0) :=
      Increment.design retainedWidth,
    select (name := .indexed "mux" 0) :=
      Mux.design (.vector retainedWidth .bit) }
  named_wires {
    roundUp := roundAnd.output }
  wiring {
    outputs {
      .result := select.result }
    instance (.retained) {
      .value := input.value }
    instance (.guardLayout) {
      .input := input.value }
    instance (.guardSplit) {
      .value := guardLayout.output }
    instance (.stickyLayout) {
      .input := input.value }
    instance (.stickySplit) {
      .value := stickyLayout.output }
    instance (.stickyAny) {
      label := from ((SignedRoundShift.context retainedWidth discardedWidth).instanceOutput
        .stickySplit (Any.inputIndex discardedWidth label)) }
    instance (.retainedLsbLayout) {
      .input := input.value }
    instance (.retainedLsbSplit) {
      .value := retainedLsbLayout.output }
    instance (.roundOr) {
      .left := stickyAny.output,
      .right := from ((SignedRoundShift.context retainedWidth discardedWidth).instanceOutput
        .retainedLsbSplit SignedRoundShift.Internal.firstBit) }
    instance (.roundAnd) {
      .left := from ((SignedRoundShift.context retainedWidth discardedWidth).instanceOutput
        .guardSplit SignedRoundShift.Internal.firstBit),
      .right := roundOr.output }
    instance (.increment) {
      .value := retained.result }
    instance (.select) {
      .select := roundAnd.output,
      .whenFalse := retained.result,
      .whenTrue := increment.result }
  }

end Silean.Modules
