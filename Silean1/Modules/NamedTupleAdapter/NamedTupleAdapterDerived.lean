import Silean.Modules.NamedTupleAdapter.Internal.NamedTupleAdapterVerification

/-! Public named-tuple adapter declarations backed by generated internals. -/

namespace Silean.Modules.NamedTupleCombiner

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

def namingWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.ModuleNaming (moduleStructure signals) :=
  (naming signals).withPorts (Naming.ports signals typeNaming)

@[reducible] def designWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.NamedModule :=
  ⟨ports signals, moduleStructure signals, namingWith signals typeNaming⟩

noncomputable def placeNamedWith (name : Naming.SourceName)
    (signals : SignalMap) (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (designWith signals typeNaming) values
  pure (child .value)

noncomputable def placeNamed (name : Naming.SourceName) (signals : SignalMap)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) :=
  placeNamedWith name signals (.positional signals.tupleType) values

noncomputable def placeWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← placeIndexed "named_tuple_combiner"
    (designWith signals typeNaming) values
  pure (child .value)

noncomputable def place (signals : SignalMap)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← placeIndexed "named_tuple_combiner" (design signals) values
  pure (child .value)

attribute [circuit_description] placeNamedWith placeNamed placeWith place

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

/-- The generated combiner implements its exact packing contract. -/
theorem implements_contract (signals : SignalMap) :
    Contracts.Cycle.Implements (moduleStructure signals) (cycleContract signals)
      (certification signals).stateCorresponds :=
  (certification signals).implements

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

def namingWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.ModuleNaming (moduleStructure signals) :=
  (naming signals).withPorts (Naming.ports signals typeNaming)

@[reducible] def designWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.NamedModule :=
  ⟨ports signals, moduleStructure signals, namingWith signals typeNaming⟩

noncomputable def placeNamedWith (name : Naming.SourceName)
    (signals : SignalMap) (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (designWith signals typeNaming) fun | .value => value
  pure child

noncomputable def placeNamed (name : Naming.SourceName) (signals : SignalMap)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) :=
  placeNamedWith name signals (.positional signals.tupleType) value

noncomputable def placeWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← placeIndexed "named_tuple_splitter"
    (designWith signals typeNaming) fun | .value => value
  pure child

noncomputable def place (signals : SignalMap) (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← placeIndexed "named_tuple_splitter" (design signals)
    (fun | .value => value)
  pure child

attribute [circuit_description] placeNamedWith placeNamed placeWith place

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

/-- The generated splitter implements its exact unpacking contract. -/
theorem implements_contract (signals : SignalMap) :
    Contracts.Cycle.Implements (moduleStructure signals) (cycleContract signals)
      (certification signals).stateCorresponds :=
  (certification signals).implements

end Silean.Modules.NamedTupleSplitter
