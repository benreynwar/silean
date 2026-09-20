import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.TupleField.TupleField
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.TupleField.Internal

open Silean

def splitter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

end Silean.Modules.TupleField.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design TupleField (signals : SignalMap) (field : signals.Label)
    (specialization := [.signalType signals.tupleType,
      .natural (signals.tuplePosition field).ordinal])
    with (typeNaming : Naming.SignalTypeNaming signals.tupleType :=
      .positional signals.tupleType) where
  boundary (TupleField.ports signals field)
    (naming := TupleField.Naming.ports signals field)
    (namingWith := TupleField.Naming.portsWithNaming signals field typeNaming)
  instances {
    split (naming := Naming.SignalAdapter.splitterWithNaming
      (.tuple signals.tupleFields) typeNaming) :=
      Naming.SignalAdapter.splitterDesign
        (TupleField.Internal.splitter signals) }
  wiring {
    outputs {
      .field := from (SignalSource.castType (signals.typeAt_tuplePosition field)
        (c.instanceOutput .split (signals.tuplePosition field))) }
    instance (.split) {
      .value := input.tuple }
  }

end Silean.Modules
