import Silean.Modules.NamedTupleAdapter.Internal.NamedTupleAdapterVerification

/-! # Named-tuple adapter theorems

These are the supported proof interfaces for translating between named signal
maps and their canonical tuple representation. Positional adapter wiring and
proof schedules remain internal.
-/

namespace Silean.Modules.NamedTupleCombiner

open Silean

/-- Every realizable combiner step packs its named inputs into one tuple. -/
theorem value_of_realization (signals : SignalMap)
    {step : (moduleStructure signals).Step}
    (realizes : (moduleStructure signals).Realizes step) :
    step.outputs .value = combinedValue signals step.inputs := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signals).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signals).allows_of_realizes
      contractState step corresponds realizes
  exact value_of_allowed signals allowed

/-- The named-tuple combiner implements its exact packing contract. -/
theorem implements_contract (signals : SignalMap) :
    Contracts.Cycle.Implements (moduleStructure signals) (cycleContract signals)
      (certification signals).stateCorresponds :=
  (certification signals).implements

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean

/-- Every realizable splitter step exposes all fields of the input tuple. -/
theorem outputs_of_realization (signals : SignalMap)
    {step : (moduleStructure signals).Step}
    (realizes : (moduleStructure signals).Realizes step) :
    step.outputs = splitValue signals (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signals).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signals).allows_of_realizes
      contractState step corresponds realizes
  exact outputs_of_allowed signals allowed

/-- The named-tuple splitter implements its exact unpacking contract. -/
theorem implements_contract (signals : SignalMap) :
    Contracts.Cycle.Implements (moduleStructure signals) (cycleContract signals)
      (certification signals).stateCorresponds :=
  (certification signals).implements

end Silean.Modules.NamedTupleSplitter
