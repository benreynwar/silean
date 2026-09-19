import Silean.Authoring.CircuitSelection
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.Register.Register
import Silean.Naming.SignalAdapterNaming

/-! Concise authoring vocabulary for the aggregate operations used throughout
PicoRV. These are opt-in aliases; canonical placement APIs remain in their
owning Silean module namespaces. -/

namespace PicoRV.Authoring.CircuitLogic

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription

/-- Place a constant using the shared Silean authoring vocabulary. Re-exported
here so PicoRV authoring files need open only one project vocabulary. -/
noncomputable abbrev constant (signalType : SignalType)
    (value : signalType.Denote) : Builder (Net signalType) :=
  Silean.Authoring.CircuitLogic.constant signalType value

/-- Split an authored named tuple into its typed fields, using a conventional
indexed instance name. -/
noncomputable abbrev split (layout : SignalLayout)
    (value : Net (SignalLayout.signalMap layout).tupleType) :
    Builder ((label : (SignalLayout.signalMap layout).Label) →
      Net ((SignalLayout.signalMap layout).signalType label)) :=
  Modules.NamedTupleSplitter.placeWith (SignalLayout.signalMap layout)
    (SignalLayout.schema layout) value

/-- Split an authored named tuple under an explicit structural instance name. -/
noncomputable abbrev splitNamed (name : Naming.SourceName)
    (layout : SignalLayout)
    (value : Net (SignalLayout.signalMap layout).tupleType) :
    Builder ((label : (SignalLayout.signalMap layout).Label) →
      Net ((SignalLayout.signalMap layout).signalType label)) :=
  Modules.NamedTupleSplitter.placeNamedWith name
    (SignalLayout.signalMap layout) (SignalLayout.schema layout) value

/-- Expose the elements of a vector through a conventionally named splitter. -/
noncomputable def splitVector (length : Nat)
    (element : SignalType) (value : Net (.vector length element)) :
    Builder ((index : Fin length) → Net element) := do
  let splitter : Silean.Composition.SignalSplitter := .vector length element
  let child ← Silean.Authoring.CircuitDescription.placeIndexed "vector_splitter"
    (Silean.Naming.SignalAdapter.splitterDesign splitter) fun
      | .value => value
  pure child

/-- Expose vector elements under an explicit structural instance name. -/
noncomputable def splitVectorNamed (name : Naming.SourceName) (length : Nat)
    (element : SignalType) (value : Net (.vector length element)) :
    Builder ((index : Fin length) → Net element) := do
  let splitter : Silean.Composition.SignalSplitter := .vector length element
  let child ← Silean.Authoring.CircuitDescription.placeNamed name
    (Silean.Naming.SignalAdapter.splitterDesign splitter) fun
      | .value => value
  pure child

/-- Combine typed fields using a conventional indexed instance name. -/
noncomputable abbrev combine (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) :=
  Modules.NamedTupleCombiner.placeWith signals typeNaming values

/-- Combine typed fields under an explicit structural instance name. -/
noncomputable abbrev combineNamed (name : Naming.SourceName)
    (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) :=
  Modules.NamedTupleCombiner.placeNamedWith name signals typeNaming values

/-- Recombine named fields after replacing only the selected values. This is
the circuit-authoring analogue of a record update: `original` supplies every
field and `overrides` returns `some` only where the circuit changes it. -/
noncomputable def update (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (original : (label : signals.Label) → Net (signals.signalType label))
    (overrides : (label : signals.Label) → Option (Net (signals.signalType label))) :
    Builder (Net signals.tupleType) :=
  combine signals typeNaming fun label =>
    (overrides label).getD (original label)

/-- Recombine named fields after selected replacements under an explicit
structural instance name. -/
noncomputable def updateNamed (name : Naming.SourceName) (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (original : (label : signals.Label) → Net (signals.signalType label))
    (overrides : (label : signals.Label) → Option (Net (signals.signalType label))) :
    Builder (Net signals.tupleType) :=
  combineNamed name signals typeNaming fun label =>
    (overrides label).getD (original label)

/-- Select between two values. The result type chooses the bit-specific or
generic mux module automatically. -/
noncomputable abbrev mux [operation :
    Silean.Authoring.CircuitLogic.MuxPlacement signalType]
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) :=
  Silean.Authoring.CircuitLogic.mux select whenFalse whenTrue

/-- Place an aggregate mux under an explicit instance name while retaining
the aggregate's authored field names. -/
noncomputable abbrev muxNamed (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming signalType)
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) :=
  Modules.Mux.placeNamedWith name typeNaming select whenFalse whenTrue

/-- Place an aggregate register with a conventional indexed instance name. -/
noncomputable abbrev register
    (typeNaming : Naming.SignalTypeNaming signalType) (value : Net signalType) :
    Builder (Net signalType) :=
  Modules.Register.placeWith typeNaming value

/-- Place an aggregate register under an explicit structural instance name. -/
noncomputable abbrev registerNamed (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming signalType) (value : Net signalType) :
    Builder (Net signalType) :=
  Modules.Register.placeNamedWith name typeNaming value

attribute [circuit_description]
  constant split splitNamed splitVector splitVectorNamed combine combineNamed
  update updateNamed mux muxNamed register registerNamed

end PicoRV.Authoring.CircuitLogic
