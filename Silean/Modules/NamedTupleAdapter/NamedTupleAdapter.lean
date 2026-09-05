import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean

/-! Named tuple adapters are authored-boundary wrappers around the canonical
positional tuple adapters. Their public component ports retain a `SignalMap`'s
labels; the only child structure depends on the tuple's `SignalType` alone. -/

inductive NamedTupleAdapterInstance
  | adapter
deriving Enumeration

namespace NamedTupleCombiner

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨signals, Composition.aggregateSignalMap signals.tupleType⟩

@[reducible] private def adapter (signals : SignalMap) : Composition.SignalCombiner :=
  .tuple signals.tupleFields

@[reducible] def instancePorts (signals : SignalMap) : InstancePorts :=
  EnumeratedMap.of NamedTupleAdapterInstance fun | .adapter => (adapter signals).ports

@[reducible] def context (signals : SignalMap) : EndpointContext :=
  ⟨ports signals, instancePorts signals⟩

def wiring (signals : SignalMap) : Wiring (context signals).ports
    (context signals).instancePorts :=
  let c := context signals
  { moduleOutput := fun | .value => c.instanceOutput .adapter .value
    instanceInput := fun
      | .adapter, position => SignalSource.castType
        (signals.allSelection.signalType_labelAt position).symm
        (c.moduleInput (signals.allSelection.labelAt position)) }

@[reducible] def body (signals : SignalMap) : ModuleBody :=
  ⟨context signals, wiring signals⟩

@[reducible] def moduleStructure (signals : SignalMap) :
    ModuleStructure (ports signals) :=
  .composite (body signals) fun | .adapter => .combiner (adapter signals)

def combinedValue (signals : SignalMap) (values : signals.Values) :
    signals.tupleType.Denote :=
  signals.tupleFields.assemble (signals.allSelection.valueAt values)

@[simp] theorem combinedValue_eq_pack (signals : SignalMap)
    (values : signals.Values) :
    combinedValue signals values = signals.pack values :=
  signals.allSelection.assemble_valueAt values

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

def naming (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) :
    ModuleNaming (moduleStructure signals) :=
  .composite ⟨"TupleCombiner", "named", [.signalType signals.tupleType]⟩
    (ports signals typeNaming)
    (fun (_ : NamedTupleAdapterInstance) => "adapter")
    (fun (_ : NamedTupleAdapterInstance) =>
      Silean.Naming.SignalAdapter.combiner
        (NamedTupleCombiner.adapter signals))

def design (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) : NamedModule :=
  ⟨NamedTupleCombiner.ports signals, moduleStructure signals,
    naming signals typeNaming⟩

end Naming
end NamedTupleCombiner

namespace NamedTupleSplitter

@[reducible] def ports (signals : SignalMap) : ModulePorts :=
  ⟨Composition.aggregateSignalMap signals.tupleType, signals⟩

@[reducible] private def adapter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

@[reducible] def instancePorts (signals : SignalMap) : InstancePorts :=
  EnumeratedMap.of NamedTupleAdapterInstance fun | .adapter => (adapter signals).ports

@[reducible] def context (signals : SignalMap) : EndpointContext :=
  ⟨ports signals, instancePorts signals⟩

def wiring (signals : SignalMap) : Wiring (context signals).ports
    (context signals).instancePorts :=
  let c := context signals
  { moduleOutput := fun label =>
      SignalSource.castType (signals.typeAt_tuplePosition label)
        (c.instanceOutput .adapter (signals.tuplePosition label))
    instanceInput := fun | .adapter, .value => c.moduleInput .value }

@[reducible] def body (signals : SignalMap) : ModuleBody :=
  ⟨context signals, wiring signals⟩

@[reducible] def moduleStructure (signals : SignalMap) :
    ModuleStructure (ports signals) :=
  .composite (body signals) fun | .adapter => .splitter (adapter signals)

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

def naming (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) :
    ModuleNaming (moduleStructure signals) :=
  .composite ⟨"TupleSplitter", "named", [.signalType signals.tupleType]⟩
    (ports signals typeNaming)
    (fun (_ : NamedTupleAdapterInstance) => "adapter")
    (fun (_ : NamedTupleAdapterInstance) =>
      Silean.Naming.SignalAdapter.splitter
        (NamedTupleSplitter.adapter signals))

def design (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType) : NamedModule :=
  ⟨NamedTupleSplitter.ports signals, moduleStructure signals,
    naming signals typeNaming⟩

end Naming
end NamedTupleSplitter

end Silean.Modules
