import Silean.Authoring.ModuleCycleContract
import Silean.Naming.SignalAdapterNaming

/-! # Named tuple adapters

These modules translate between a `SignalMap`'s named fields and its canonical
tuple representation.
-/

namespace Silean.Modules.NamedTupleCombiner

open Silean
open Silean.Authoring

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨signals, Composition.aggregateSignalMap signals.tupleType⟩

namespace Naming

open Silean.Naming

def ports (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) :
    ModulePortsNaming (NamedTupleCombiner.ports signals) where
  inputs := ⟨fun label => match typeNaming with
    | .tuple fields => fields.nameAt (signals.tuplePosition label)⟩
  outputs := ⟨fun | .value => "value"⟩
  inputTypes := fun label =>
    SignalAdapter.tupleFieldNaming signals typeNaming label
  outputTypes := fun | .value => typeNaming

end Naming

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

/-- Every allowed combiner step packs the named inputs into one tuple. -/
theorem value_of_allowed (signals : SignalMap)
    {step : (cycleContract signals).Step}
    (allowed : (cycleContract signals).Allows step) :
    step.outputs .value = combinedValue signals step.inputs :=
  (outputRule_holds_iff signals step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean
open Silean.Authoring

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨Composition.aggregateSignalMap signals.tupleType, signals⟩

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
    SignalAdapter.tupleFieldNaming signals typeNaming label

end Naming

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

/-- Every allowed splitter step exposes every named tuple field. -/
theorem outputs_of_allowed (signals : SignalMap)
    {step : (cycleContract signals).Step}
    (allowed : (cycleContract signals).Allows step) :
    step.outputs = splitValue signals (step.inputs .value) :=
  (outputRule_holds_iff signals step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end Silean.Modules.NamedTupleSplitter
