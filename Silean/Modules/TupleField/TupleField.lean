import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Select one field from a named tuple. The field label itself carries the
evidence for the selected signal type, so hardware descriptions never need to
translate a name into a positional tuple index. The dependent field type and
its cast are most visible in the typed `module_design`; a fixed builder form
would only hide that relationship behind another representation. -/

module_design TupleField (signals : SignalMap) (field : signals.Label)
    (specialization := [.signalType signals.tupleType,
      .natural (signals.tuplePosition field).ordinal])
    with (typeNaming : Naming.SignalTypeNaming signals.tupleType :=
      .positional signals.tupleType) where
  ports {
    input tuple (schema := typeNaming) : signals.tupleType,
    output field (schema := Naming.SignalAdapter.tupleFieldNaming signals
      typeNaming field) : signals.signalType field }
  instances {
    split (naming := Silean.Naming.SignalAdapter.splitterWithNaming
      (.tuple signals.tupleFields) typeNaming) :=
      Silean.Naming.SignalAdapter.splitterDesign (.tuple signals.tupleFields) }
  wiring {
    outputs {
      .field := from (SignalSource.castType (signals.typeAt_tuplePosition field)
        (c.instanceOutput .split (signals.tuplePosition field))) }
    instance (.split) {
      .value := input.tuple }
  }

end Silean.Modules

namespace Silean.Modules.TupleField

open Silean
open Silean.Authoring

def selectedValue (signals : SignalMap) (field : signals.Label)
    (value : signals.tupleType.Denote) : (signals.signalType field).Denote :=
  signals.typeAt_tuplePosition field ▸
    signals.tupleFields.get value (signals.tuplePosition field)

module_cycle_contract cycleContract (signals : SignalMap)
    (field : signals.Label) for ports signals field where
  state := emptySignalMap
  output_rule select where
    reads := [tuple]
    writes := { field := selectedValue signals field tuple }
  state_rule where
    reads := []
    next := {}

/-- Every allowed tuple-field step returns the selected field. -/
theorem field_of_allowed (signals : SignalMap) (field : signals.Label)
    {step : (cycleContract signals field).Step}
    (allowed : (cycleContract signals field).Allows step) :
    step.outputs .field = selectedValue signals field (step.inputs .tuple) :=
  (selectRule_holds_iff signals field
    step.inputs step.currentState step.outputs).mp (allowed.1 .select)

end Silean.Modules.TupleField
