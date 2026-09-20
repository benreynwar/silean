import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.CarrySaveAdder.CarrySaveAdder
import Silean.Modules.FullAdder.FullAdderDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Naming.SignalAdapterNaming

/-! Indexed structural implementation of the carry-save adder. -/

namespace Silean.Modules.CarrySaveAdder.Internal

open Silean

def splitter (width : Nat) : Composition.SignalSplitter :=
  .vector width .bit

def combiner (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

/-- Static one-bit left shift used to place carry bits at their proper weights. -/
def carryShiftLayout (width : Nat) :
    Fin width → VectorLayout.BitSource width :=
  fun index =>
    if nonzero : 0 < index.val then
      .input ⟨index.val - 1, by omega⟩
    else
      .constant false

end Silean.Modules.CarrySaveAdder.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design CarrySaveAdder (width : Nat) where
  boundary (CarrySaveAdder.ports width)
    (naming := CarrySaveAdder.Naming.ports width)
  instances {
    iASplit (name := .indexed "splitter" 0) :=
      Naming.SignalAdapter.splitterDesign
        (CarrySaveAdder.Internal.splitter width),
    iBSplit (name := .indexed "splitter" 1) :=
      Naming.SignalAdapter.splitterDesign
        (CarrySaveAdder.Internal.splitter width),
    iCSplit (name := .indexed "splitter" 2) :=
      Naming.SignalAdapter.splitterDesign
        (CarrySaveAdder.Internal.splitter width),
    adder (index : Fin width in Enumeration.fin width)
      (name := .indexed "full_adder" index.val) := FullAdder.design,
    sumCombine (name := .indexed "combiner" 0) :=
      Naming.SignalAdapter.combinerDesign
        (CarrySaveAdder.Internal.combiner width),
    rawCarryCombine (name := .indexed "combiner" 1) :=
      Naming.SignalAdapter.combinerDesign
        (CarrySaveAdder.Internal.combiner width),
    carryShift (name := .indexed "vector_layout" 0) :=
      VectorLayout.design width width
        (CarrySaveAdder.Internal.carryShiftLayout width) }
  wiring {
    outputs {
      .sum := sumCombine.value,
      .carry := carryShift.output }
    instance (.iASplit) {
      .value := input.iA }
    instance (.iBSplit) {
      .value := input.iB }
    instance (.iCSplit) {
      .value := input.iC }
    instance (.adder index) {
      .left := iASplit[index],
      .right := iBSplit[index],
      .carryIn := iCSplit[index] }
    instance (.sumCombine) {
      index := adder(index)[.sum] }
    instance (.rawCarryCombine) {
      index := adder(index)[.carryOut] }
    instance (.carryShift) {
      .input := rawCarryCombine.value }
  }

end Silean.Modules
