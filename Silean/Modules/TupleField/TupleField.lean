import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Select one field from a named tuple. The field label itself carries the
evidence for the selected signal type, so hardware descriptions never need to
translate a name into a positional tuple index. -/

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

theorem outputSourceValue (signals : SignalMap) (field : signals.Label)
    (inputs : (ports signals field).inputs.Values)
    (childOutputs : (name : (instancePorts signals field).Name) →
      ((instancePorts signals field).ports name).outputs.Values) :
    ((body signals field).wiring.moduleOutput .field).value inputs childOutputs =
      signals.typeAt_tuplePosition field ▸
        (show (signals.tupleFields.typeAt
          (signals.tuplePosition field)).Denote from
          childOutputs .split (signals.tuplePosition field)) := by
  change (SignalSource.castType (signals.typeAt_tuplePosition field)
    ((context signals field).instanceOutput .split
      (signals.tuplePosition field))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  rfl

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

theorem field_of_evaluatesTo (signals : SignalMap)
    (field : signals.Label) (inputs : (ports signals field).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signals field).outputs.Values)
    (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signals field).EvaluatesTo
      inputs state outputs nextState) :
    outputs .field = selectedValue signals field (inputs .tuple) :=
  (selectRule_holds_iff signals field inputs state outputs).mp
    (evaluates.1 .select)

end Silean.Modules.TupleField
