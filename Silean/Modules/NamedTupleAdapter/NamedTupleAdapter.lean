import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Authoring.CircuitDescription
import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.NamedTupleCombiner

open Silean

/-! A named-tuple combiner presents a `SignalMap`'s labels as separate inputs
and packs their values into the corresponding tuple. Its sole child is the
canonical positional tuple combiner; the wrapper adds readable labels, not
hardware logic.

The boundary itself is an arbitrary dependent `SignalMap` family. The typed
`module_design` directly expresses that generated family; reproducing it with
individually declared builder ports would be less direct, so no second fixed
`CircuitDescription` is maintained. -/

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨signals, Composition.aggregateSignalMap signals.tupleType⟩

def adapter (signals : SignalMap) : Composition.SignalCombiner :=
  .tuple signals.tupleFields

namespace Naming

open Silean.Naming

def ports (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) :
    ModulePortsNaming (NamedTupleCombiner.ports signals) where
  inputs := ⟨fun label => match typeNaming with
    | .tuple fields => fields.nameAt (signals.tuplePosition label)⟩
  outputs := ⟨fun | .value => "value"⟩
  inputTypes := fun label =>
    Silean.Naming.SignalAdapter.tupleFieldNaming signals typeNaming label
  outputTypes := fun | .value => typeNaming

end Naming

end Silean.Modules.NamedTupleCombiner

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
      (NamedTupleCombiner.adapter signals) }
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

namespace Silean.Modules.NamedTupleCombiner

open Silean
open Silean.Authoring

def namingWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.ModuleNaming (moduleStructure signals) :=
  (naming signals).withPorts (Naming.ports signals typeNaming)

@[reducible] def designWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.NamedModule :=
  ⟨ports signals, moduleStructure signals, namingWith signals typeNaming⟩

/-! ## Placement -/

open Authoring.CircuitDescription

/-- Place a named tuple combiner with caller-supplied aggregate naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (signals : SignalMap) (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (designWith signals typeNaming) values
  pure (child .value)

/-- Place a named tuple combiner with positional aggregate naming. -/
noncomputable def placeNamed (name : Naming.SourceName) (signals : SignalMap)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) :=
  placeNamedWith name signals (.positional signals.tupleType) values

/-- Place a named tuple combiner with caller-supplied aggregate naming and a
conventional indexed instance name. -/
noncomputable def placeWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← placeIndexed "named_tuple_combiner"
    (designWith signals typeNaming) values
  pure (child .value)

/-- Place a named tuple combiner using a conventional indexed name. -/
noncomputable def place (signals : SignalMap)
    (values : (label : signals.Label) → Net (signals.signalType label)) :
    Builder (Net signals.tupleType) := do
  let child ← placeIndexed "named_tuple_combiner" (design signals) values
  pure (child .value)

attribute [circuit_description] placeNamedWith placeNamed placeWith place

def combinedValue (signals : SignalMap) (values : signals.Values) :
    signals.tupleType.Denote :=
  signals.tupleFields.assemble (signals.allSelection.valueAt values)

@[simp] theorem combinedValue_eq_pack (signals : SignalMap)
    (values : signals.Values) :
    combinedValue signals values = signals.pack values :=
  signals.allSelection.assemble_valueAt values

def outputRule (signals : SignalMap) :
    Contracts.Cycle.CycleOutputRule (ports signals) emptySignalMap where
  readsInputs := .all signals
  writesOutputs := .all (Composition.aggregateSignalMap signals.tupleType)
  target := fun inputs _ => fun | .value => combinedValue signals inputs

module_cycle_contract cycleContract (signals : SignalMap) for ports signals where
  state := emptySignalMap
  output_rule apply := outputRule signals
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (signals : SignalMap)
    (inputs : (ports signals).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signals).outputs.Values) :
    (outputRule signals).Holds inputs state outputs ↔
      outputs .value = combinedValue signals inputs := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext label
    cases label
    exact equal

/-- Every contract-allowed combiner step packs the named inputs into their
canonical tuple representation. -/
theorem value_of_allowed (signals : SignalMap)
    {step : (cycleContract signals).Step}
    (allowed : (cycleContract signals).Allows step) :
    step.outputs .value = combinedValue signals step.inputs :=
  (outputRule_holds_iff signals step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean

/-! A named-tuple splitter accepts one tuple and exposes its fields using a
`SignalMap`'s labels. Its sole child is the canonical positional tuple splitter;
the wrapper only translates labels to their typed tuple positions. As with the
combiner, the arbitrary dependent output family is clearer in `module_design`
than as a duplicated fixed builder description. -/

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨Composition.aggregateSignalMap signals.tupleType, signals⟩

def adapter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

namespace Naming

open Silean.Naming

def ports (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) :
    ModulePortsNaming (NamedTupleSplitter.ports signals) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun label => match typeNaming with
    | .tuple fields => fields.nameAt (signals.tuplePosition label)⟩
  inputTypes := fun | .value => typeNaming
  outputTypes := fun label =>
    Silean.Naming.SignalAdapter.tupleFieldNaming signals typeNaming label

end Naming

end Silean.Modules.NamedTupleSplitter

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
      (NamedTupleSplitter.adapter signals) }
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

namespace Silean.Modules.NamedTupleSplitter

open Silean
open Silean.Authoring

def namingWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.ModuleNaming (moduleStructure signals) :=
  (naming signals).withPorts (Naming.ports signals typeNaming)

@[reducible] def designWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType) :
    Naming.NamedModule :=
  ⟨ports signals, moduleStructure signals, namingWith signals typeNaming⟩

/-! ## Placement -/

open Authoring.CircuitDescription

/-- Place a named tuple splitter with caller-supplied aggregate naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (signals : SignalMap) (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (designWith signals typeNaming) fun | .value => value
  pure child

/-- Place a named tuple splitter with positional aggregate naming. -/
noncomputable def placeNamed (name : Naming.SourceName) (signals : SignalMap)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) :=
  placeNamedWith name signals (.positional signals.tupleType) value

/-- Place a named tuple splitter with caller-supplied aggregate naming and a
conventional indexed instance name. -/
noncomputable def placeWith (signals : SignalMap)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← placeIndexed "named_tuple_splitter"
    (designWith signals typeNaming) fun | .value => value
  pure child

/-- Place a named tuple splitter using a conventional indexed name. -/
noncomputable def place (signals : SignalMap) (value : Net signals.tupleType) :
    Builder ((label : signals.Label) → Net (signals.signalType label)) := do
  let child ← placeIndexed "named_tuple_splitter" (design signals)
    (fun | .value => value)
  pure child

attribute [circuit_description] placeNamedWith placeNamed placeWith place

def splitValue (signals : SignalMap) (value : signals.tupleType.Denote) :
    signals.Values := fun label =>
  signals.typeAt_tuplePosition label ▸
    signals.tupleFields.get value (signals.tuplePosition label)

@[simp] theorem splitValue_pack (signals : SignalMap) (values : signals.Values) :
    splitValue signals (signals.pack values) = values := by
  funext label
  unfold splitValue
  change signals.typeAt_tuplePosition label ▸
      signals.tupleFields.get
        (signals.allSelection.project values) (signals.tuplePosition label) =
    values label
  rw [SignalSelection.get_project]
  exact signals.cast_valueAt_tuplePosition values label

def outputRule (signals : SignalMap) :
    Contracts.Cycle.CycleOutputRule (ports signals) emptySignalMap where
  readsInputs := .all (Composition.aggregateSignalMap signals.tupleType)
  writesOutputs := .all signals
  target := fun inputs _ => splitValue signals (inputs .value)

module_cycle_contract cycleContract (signals : SignalMap) for ports signals where
  state := emptySignalMap
  output_rule apply := outputRule signals
  state_rule := Contracts.Cycle.CycleStateRule.empty _
  output_coverage := by
    rw [show (inferInstance : Enumeration Rule).values = [.apply] by rfl]
    simp [outputRule]

@[simp] theorem outputRule_holds_iff (signals : SignalMap)
    (inputs : (ports signals).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signals).outputs.Values) :
    (outputRule signals).Holds inputs state outputs ↔
      outputs = splitValue signals (inputs .value) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds]

/-- Every contract-allowed splitter step exposes every named tuple field. -/
theorem outputs_of_allowed (signals : SignalMap)
    {step : (cycleContract signals).Step}
    (allowed : (cycleContract signals).Allows step) :
    step.outputs = splitValue signals (step.inputs .value) :=
  (outputRule_holds_iff signals step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end Silean.Modules.NamedTupleSplitter
