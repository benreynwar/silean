import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.NamedTupleCombiner

open Silean

/-! A named-tuple combiner presents a `SignalMap`'s labels as separate inputs
and packs their values into the corresponding tuple. Its sole child is the
canonical positional tuple combiner; the wrapper adds readable labels, not
hardware logic. -/

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

def combinedValue (signals : SignalMap) (values : signals.Values) :
    signals.tupleType.Denote :=
  signals.tupleFields.assemble (signals.allSelection.valueAt values)

@[simp] theorem combinedValue_eq_pack (signals : SignalMap)
    (values : signals.Values) :
    combinedValue signals values = signals.pack values :=
  signals.allSelection.assemble_valueAt values

/-- The cast in the authored wiring only transports a named input to its
definitionally corresponding positional child input. -/
theorem adapterInputValue (signals : SignalMap)
    (inputs : (ports signals).inputs.Values)
    (childOutputs : (name : (instancePorts signals).Name) →
      ((instancePorts signals).ports name).outputs.Values)
    (position : SignalTypes.Position signals.tupleFields) :
    ((wiring signals).instanceInput .adapter position).value inputs childOutputs =
      signals.allSelection.valueAt inputs position := by
  change (SignalSource.castType
    (signals.allSelection.signalType_labelAt position).symm
    ((context signals).moduleInput
      (signals.allSelection.labelAt position))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  exact signals.allSelection.cast_labelAt_value inputs position

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

end Silean.Modules.NamedTupleCombiner

namespace Silean.Modules.NamedTupleSplitter

open Silean

/-! A named-tuple splitter accepts one tuple and exposes its fields using a
`SignalMap`'s labels. Its sole child is the canonical positional tuple splitter;
the wrapper only translates labels to their typed tuple positions. -/

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

/-- The cast in the authored wiring transports a positional child output to
the corresponding named boundary output. -/
theorem moduleOutputValue (signals : SignalMap)
    (inputs : (ports signals).inputs.Values)
    (childOutputs : (name : (instancePorts signals).Name) →
      ((instancePorts signals).ports name).outputs.Values)
    (label : signals.Label) :
    ((wiring signals).moduleOutput label).value inputs childOutputs =
      signals.typeAt_tuplePosition label ▸
        childOutputs .adapter (signals.tuplePosition label) := by
  change (SignalSource.castType (signals.typeAt_tuplePosition label)
    ((context signals).instanceOutput .adapter
      (signals.tuplePosition label))).value inputs childOutputs = _
  rw [SignalSource.value_castType]
  rfl

theorem castOutput_congr (signals : SignalMap) (label : signals.Label)
    (left right : (position : SignalTypes.Position signals.tupleFields) →
      (signals.tupleFields.typeAt position).Denote)
    (equal : left = right) :
    signals.typeAt_tuplePosition label ▸
        left (signals.tuplePosition label) =
      signals.typeAt_tuplePosition label ▸
        right (signals.tuplePosition label) := by
  rw [equal]

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

end Silean.Modules.NamedTupleSplitter
