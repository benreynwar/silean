import Silean.Modules.Mux.Internal.MuxVerification

/-! Public multiplexer declarations backed by generated internals. -/

namespace Silean.Modules.Mux

open Silean
open Authoring.CircuitDescription

/-- Place a mux under a caller-chosen instance name and aggregate naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming signalType)
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) := do
  let outputs ← ports.placeNamed signalType name
    (moduleStructure signalType) (namingWith signalType typeNaming)
    select whenFalse whenTrue
  pure outputs.result

/-- Place a mux under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) :=
  placeNamedWith name (.positional signalType) select whenFalse whenTrue

/-- Place a mux using the next conventional indexed name. -/
noncomputable def place (select : Net .bit)
    (whenFalse whenTrue : Net signalType) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "mux"
    (moduleStructure signalType) (naming signalType)
    select whenFalse whenTrue
  pure outputs.result

attribute [circuit_description] placeNamedWith placeNamed place

/-- The authored mux implements its exact selection contract. -/
theorem construction_correct (signalType : SignalType) :
    (description signalType).ImplementsCycleContract
      (cycleContract signalType) (Naming.ports signalType) :=
  Internal.construction_correct signalType

/-- Every realizable mux step selects the requested input. -/
theorem result_of_realization (signalType : SignalType)
    {step : (moduleStructure signalType).Step}
    (realizes : (moduleStructure signalType).Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Internal.result_of_realization signalType realizes

/-- The generated hierarchy implements the exact mux contract. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements (moduleStructure signalType)
      (cycleContract signalType) (certification signalType).stateCorresponds :=
  (certification signalType).implements

end Silean.Modules.Mux
