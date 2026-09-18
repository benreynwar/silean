import Silean.Modules.Mux.Internal.MuxVerification

/-! # Mux correctness

`Mux.lean` gives the authored circuit and its exact cycle specification. The
theorems here state the public correctness connection between them. The child
certifications, schedule, Boolean identity, and structural correspondence
proofs used below remain in `Internal/MuxVerification.lean`.
-/

namespace Silean.Modules.Mux.Description

open Silean Naming Authoring.CircuitDescription

/-- The circuit authored in `Mux.lean` is exactly the named structural Mux
whose implementation is certified against `Mux.cycleContract`. -/
theorem authored_definition_corresponds (signalType : SignalType) :
    Corresponds (description signalType) (Mux.naming signalType) :=
  Internal.corresponds signalType

/-- Every realizable boundary step of the authored Mux selects `whenTrue` when
`select` is high and `whenFalse` otherwise. Together with
`authored_definition_corresponds`, this is the correctness theorem for the
definition in `Mux.lean`. -/
theorem result_of_realization (signalType : SignalType)
    {step : (Mux.moduleStructure signalType).Step}
    (realizes : (Mux.moduleStructure signalType).Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Mux.Internal.result_of_realization signalType realizes

end Silean.Modules.Mux.Description

namespace Silean.Modules.Mux

open Silean

/-- The concrete Mux structure implements its exact cycle contract at the
shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=

    (certification signalType).implements

end Silean.Modules.Mux
