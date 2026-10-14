import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Naming.SignalAdapterNaming

/-! # Tuple field

`TupleField` selects one typed field from a named tuple.
-/

namespace Silean.Modules.TupleField

open Silean
open Silean.Authoring

module_ports ports (signals : SignalMap) (field : signals.Label)
    with (typeNaming : Naming.SignalTypeNaming signals.tupleType :=
      .positional signals.tupleType) where
  input tuple (schema := typeNaming) : signals.tupleType,
  output field (schema := Naming.SignalAdapter.tupleFieldNaming signals
    typeNaming field) : signals.signalType field

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

end Silean.Modules.TupleField
