import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.CarrySaveAdder.CarrySaveAdderDerived
import Silean.Modules.CarrySaveLayer.CarrySaveLayer
import Silean.Modules.CarrySaveLayer.Internal.CarrySaveLayerLayout
import Silean.Modules.VectorReindex.VectorReindexDerived
import Silean.Naming.SignalAdapterNaming

/-! Indexed structural implementation of one carry-save compression layer. -/

namespace Silean.Modules.CarrySaveLayer.Internal

open Silean

@[reducible] def splitter (width operandCount : Nat) : Composition.SignalSplitter :=
  .vector operandCount (.vector width .bit)

@[reducible] def combiner (width operandCount : Nat) : Composition.SignalCombiner :=
  .vector (reducedCount operandCount) (.vector width .bit)

/-- Evaluating the flat collection of structural sources is the same as
flattening their values. -/
theorem flatten_source_value {context : EndpointContext}
    {signalType : SignalType} (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) →
      SignalSource context.ports context.instancePorts signalType)
    (remainder : Fin (remainderCount operandCount) →
      SignalSource context.ports context.instancePorts signalType)
    (inputs : context.ports.inputs.Values)
    (childOutputs : (child : context.instancePorts.Name) →
      (context.instancePorts.ports child).outputs.Values)
    (index : Fin (reducedCount operandCount)) :
    (flatten operandCount sums carries remainder index).value
        inputs childOutputs =
      flatten operandCount
        (fun group => (sums group).value inputs childOutputs)
        (fun group => (carries group).value inputs childOutputs)
        (fun rest => (remainder rest).value inputs childOutputs) index :=
  map_flatten (fun source => source.value inputs childOutputs)
    operandCount sums carries remainder index

end Silean.Modules.CarrySaveLayer.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design CarrySaveLayer (width : Nat) (operandCount : Nat) where
  boundary (CarrySaveLayer.ports width operandCount)
    (naming := CarrySaveLayer.Naming.ports width operandCount)
  instances {
    split := Naming.SignalAdapter.splitterDesign
      (CarrySaveLayer.Internal.splitter width operandCount),
    adder (group : Fin (CarrySaveLayer.groupCount operandCount) in
        Enumeration.fin (CarrySaveLayer.groupCount operandCount))
      (name := .indexed "carry_save_adder" group.val) :=
        CarrySaveAdder.design width,
    combine := Naming.SignalAdapter.combinerDesign
      (CarrySaveLayer.Internal.combiner width operandCount),
    reindex := VectorReindex.design (.vector width .bit)
      (CarrySaveLayer.reducedCount operandCount)
      (CarrySaveLayer.reducedCount operandCount)
      (CarrySaveLayer.Internal.interleaveLayout operandCount) }
  wiring {
    outputs {
      .reduced := reindex.output }
    instance (.split) {
      .value := input.operands }
    instance (.adder group) {
      .iA := split[CarrySaveLayer.Internal.groupedInputIndex
        operandCount group 0],
      .iB := split[CarrySaveLayer.Internal.groupedInputIndex
        operandCount group 1],
      .iC := split[CarrySaveLayer.Internal.groupedInputIndex
        operandCount group 2] }
    instance (.combine) {
      index := from (CarrySaveLayer.Internal.flatten operandCount
        (fun group =>
          (CarrySaveLayer.context width operandCount).instanceOutput
            (.adder group) .sum
        )
        (fun group =>
          (CarrySaveLayer.context width operandCount).instanceOutput
            (.adder group) .carry
        )
        (fun remainder =>
          (CarrySaveLayer.context width operandCount).instanceOutput .split
            (CarrySaveLayer.Internal.remainderInputIndex
              operandCount remainder))
        index) }
    instance (.reindex) {
      .input := combine.value }
  }

end Silean.Modules
