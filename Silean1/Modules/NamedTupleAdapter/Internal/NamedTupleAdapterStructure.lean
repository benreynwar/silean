import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Modules.NamedTupleCombiner.Internal

open Silean

def adapter (signals : SignalMap) : Composition.SignalCombiner :=
  .tuple signals.tupleFields

end Silean.Modules.NamedTupleCombiner.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design NamedTupleCombiner (signals : SignalMap)
    (specialization := [.signalType signals.tupleType]) where
  boundary (NamedTupleCombiner.ports signals)
    (naming := NamedTupleCombiner.Naming.ports signals
      (.positional signals.tupleType))
  instances {
    adapter := Naming.SignalAdapter.combinerDesign
      (NamedTupleCombiner.Internal.adapter signals) }
  wiring {
    outputs {
      .value := adapter.value }
    instance (.adapter) {
      position := from (SignalSource.castType
        (signals.allSelection.signalType_labelAt position).symm
        ((NamedTupleCombiner.context signals).moduleInput
          (signals.allSelection.labelAt position))) }
  }

end Silean.Modules

namespace Silean.Modules.NamedTupleSplitter.Internal

open Silean

def adapter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

end Silean.Modules.NamedTupleSplitter.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design NamedTupleSplitter (signals : SignalMap)
    (specialization := [.signalType signals.tupleType]) where
  boundary (NamedTupleSplitter.ports signals)
    (naming := NamedTupleSplitter.Naming.ports signals
      (.positional signals.tupleType))
  instances {
    adapter := Naming.SignalAdapter.splitterDesign
      (NamedTupleSplitter.Internal.adapter signals) }
  wiring {
    outputs {
      label := from (SignalSource.castType
        (signals.typeAt_tuplePosition label)
        ((NamedTupleSplitter.context signals).instanceOutput .adapter
          (signals.tuplePosition label))) }
    instance (.adapter) {
      .value := input.value }
  }

end Silean.Modules
