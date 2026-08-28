import Silean.SignalLayout
import Silean.PrimitivePorts

namespace Silean

inductive AggregatePort
  | value
deriving Enumeration

@[reducible] def aggregateSignalMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of AggregatePort fun | .value => signalType

inductive SignalSplitter where
  | vector (length : Nat) (element : SignalType)
  | tuple (fields : SignalTypes)

inductive SignalCombiner where
  | vector (length : Nat) (element : SignalType)
  | tuple (fields : SignalTypes)

namespace SignalSplitter

@[reducible] def aggregateType : SignalSplitter → SignalType
  | .vector length element => .vector length element
  | .tuple fields => .tuple fields

@[reducible] def combiner : SignalSplitter → SignalCombiner
  | .vector length element => .vector length element
  | .tuple fields => .tuple fields

@[reducible] def ports : SignalSplitter → ModulePorts
  | .vector length element =>
      ⟨aggregateSignalMap (.vector length element), SignalType.vectorComponents length element⟩
  | .tuple fields => ⟨aggregateSignalMap (.tuple fields), fields.componentMap⟩

def outputValues : (splitter : SignalSplitter) →
    splitter.ports.inputs.Values → splitter.ports.outputs.Values
  | .vector _ _, inputs => fun index => inputs .value index
  | .tuple fields, inputs => fields.get (inputs .value)

def inputValues : (splitter : SignalSplitter) →
    splitter.aggregateType.Denote → splitter.ports.inputs.Values
  | .vector _ _, value => fun | .value => value
  | .tuple _, value => fun | .value => value

end SignalSplitter

namespace SignalCombiner

@[reducible] def aggregateType : SignalCombiner → SignalType
  | .vector length element => .vector length element
  | .tuple fields => .tuple fields

@[reducible] def ports : SignalCombiner → ModulePorts
  | .vector length element =>
      ⟨SignalType.vectorComponents length element, aggregateSignalMap (.vector length element)⟩
  | .tuple fields => ⟨fields.componentMap, aggregateSignalMap (.tuple fields)⟩

def outputValues : (combiner : SignalCombiner) →
    combiner.ports.inputs.Values → combiner.ports.outputs.Values
  | .vector _ _, inputs => fun | .value => fun index => inputs index
  | .tuple fields, inputs => fun | .value => fields.assemble inputs

def combinedValue : (combiner : SignalCombiner) →
    combiner.ports.inputs.Values → combiner.aggregateType.Denote
  | .vector _ _, inputs => fun index => inputs index
  | .tuple fields, inputs => fields.assemble inputs

def outputValue : (combiner : SignalCombiner) →
    combiner.ports.outputs.Values → combiner.aggregateType.Denote
  | .vector _ _, outputs => outputs .value
  | .tuple _, outputs => outputs .value

end SignalCombiner

namespace SignalSplitter

def combineComponents : (splitter : SignalSplitter) →
    splitter.ports.outputs.Values → splitter.aggregateType.Denote
  | .vector _ _, components => fun index => components index
  | .tuple fields, components => fields.assemble components

theorem split_combined (splitter : SignalSplitter)
    (components : splitter.ports.outputs.Values) :
    splitter.outputValues
      (splitter.inputValues (splitter.combineComponents components)) =
        components := by
  cases splitter with
  | vector => rfl
  | tuple fields => exact fields.get_assemble components

theorem combine_split (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote) :
    splitter.combineComponents
      (splitter.outputValues (splitter.inputValues value)) = value := by
  cases splitter with
  | vector => rfl
  | tuple fields => exact fields.assemble_get value

end SignalSplitter

namespace SignalComponent

def inputReads (componentPorts : ModulePorts) : List componentPorts.inputs.Label :=
  componentPorts.inputs.labels.values

def outputWrites (componentPorts : ModulePorts) : List componentPorts.outputs.Label :=
  componentPorts.outputs.labels.values

theorem inputs_equal_of_agree (componentPorts : ModulePorts)
    (left right : componentPorts.inputs.Values)
    (agree : ∀ input, input ∈ inputReads componentPorts →
      left input = right input) : left = right := by
  funext input
  exact agree input (ListIndex.get_eq
    (componentPorts.inputs.labels.locate input) ▸
      List.get_mem _ _)

end SignalComponent

end Silean
