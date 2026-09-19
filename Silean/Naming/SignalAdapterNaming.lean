import Silean.Naming.ModuleNaming
import Silean.Foundation.SignalLayout

namespace Silean.Naming.SignalAdapter

open Silean Silean.Composition Silean.Naming

def tupleFieldNaming (signals : SignalMap)
    (typeNaming : SignalTypeNaming signals.tupleType)
    (field : signals.Label) : SignalTypeNaming (signals.signalType field) := by
  change SignalTypeNaming (.tuple signals.tupleFields) at typeNaming
  cases typeNaming with
  | tuple fieldNaming =>
      have result := fieldNaming.typeAt (signals.tuplePosition field)
      rw [signals.typeAt_tuplePosition] at result
      exact result

def splitterPortsWithNaming : (splitter : Composition.SignalSplitter) →
    SignalTypeNaming splitter.aggregateType → ModulePortsNaming splitter.ports
  | .vector length elementType, aggregateNaming =>
      { inputs := .indexed
          (aggregateSignalMap (.vector length elementType)) "aggregate"
        outputs := ⟨fun component => .indexed "component" component.val⟩
        inputTypes := fun | .value => aggregateNaming
        outputTypes := fun component => aggregateNaming.component component }
  | .tuple fields, .tuple fieldNaming =>
      { inputs := .indexed (aggregateSignalMap (.tuple fields)) "aggregate"
        outputs := ⟨fun field =>
          fieldNaming.nameAt field⟩
        inputTypes := fun | .value => .tuple fieldNaming
        outputTypes := fun field => fieldNaming.typeAt field }

def combinerPortsWithNaming : (combiner : Composition.SignalCombiner) →
    SignalTypeNaming combiner.aggregateType → ModulePortsNaming combiner.ports
  | .vector length elementType, aggregateNaming =>
      { inputs := ⟨fun component => .indexed "component" component.val⟩
        outputs := .indexed
          (aggregateSignalMap (.vector length elementType)) "aggregate"
        inputTypes := fun component => aggregateNaming.component component
        outputTypes := fun | .value => aggregateNaming }
  | .tuple fields, .tuple fieldNaming =>
      { inputs := ⟨fun field =>
          fieldNaming.nameAt field⟩
        outputs := .indexed (aggregateSignalMap (.tuple fields)) "aggregate"
        inputTypes := fun field => fieldNaming.typeAt field
        outputTypes := fun | .value => .tuple fieldNaming }

def splitterPorts (splitter : Composition.SignalSplitter) : ModulePortsNaming splitter.ports :=
  splitterPortsWithNaming splitter (.positional splitter.aggregateType)

def combinerPorts (combiner : Composition.SignalCombiner) : ModulePortsNaming combiner.ports :=
  combinerPortsWithNaming combiner (.positional combiner.aggregateType)

def splitterWithNaming (value : Composition.SignalSplitter)
    (aggregateNaming : SignalTypeNaming value.aggregateType) :
    ModuleNaming (.splitter value) :=
  .splitter value ⟨"split", "aggregate", [.signalType value.aggregateType]⟩
    (splitterPortsWithNaming value aggregateNaming)

def combinerWithNaming (value : Composition.SignalCombiner)
    (aggregateNaming : SignalTypeNaming value.aggregateType) :
    ModuleNaming (.combiner value) :=
  .combiner value ⟨"combine", "aggregate", [.signalType value.aggregateType]⟩
    (combinerPortsWithNaming value aggregateNaming)

def splitter (value : Composition.SignalSplitter) : ModuleNaming (.splitter value) :=
  splitterWithNaming value (.positional value.aggregateType)

def combiner (value : Composition.SignalCombiner) : ModuleNaming (.combiner value) :=
  combinerWithNaming value (.positional value.aggregateType)

/-- The default names of a vector combiner are collision-free for every
symbolic vector length. This is useful when a fixed composite places the
combiner through the checked circuit-description interface. -/
theorem vectorCombiner_portNames_nodup (length : Nat) (elementType : SignalType) :
    (combiner (.vector length elementType)).ports.names.Nodup := by
  change
    ((List.finRange length).map
      (fun component => SourceName.indexed "component" component.val) ++
      [SourceName.indexed "aggregate" 0]).Nodup
  rw [List.nodup_append]
  constructor
  · exact List.nodup_map_of_injective _ (by
      intro left right equal
      cases SourceName.indexed.inj equal
      exact Fin.ext (by assumption)) (List.finRange_nodup length)
  constructor
  · simp
  · intro componentName inComponents aggregateName inAggregate equal
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inAggregate
    rcases List.mem_map.mp inComponents with ⟨component, _, componentEqual⟩
    rw [← componentEqual, inAggregate] at equal
    have stemEqual := (SourceName.indexed.inj equal).1
    simp at stemEqual

/-- The default names of a vector splitter are collision-free for every
symbolic vector length. -/
theorem vectorSplitter_portNames_nodup (length : Nat) (elementType : SignalType) :
    (splitter (.vector length elementType)).ports.names.Nodup := by
  change
    ([SourceName.indexed "aggregate" 0] ++
      (List.finRange length).map
        (fun component => SourceName.indexed "component" component.val)).Nodup
  rw [List.nodup_append]
  constructor
  · simp
  constructor
  · exact (List.nodup_append.mp
      (vectorCombiner_portNames_nodup length elementType)).1
  · intro aggregateName inAggregate componentName inComponents equal
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inAggregate
    rcases List.mem_map.mp inComponents with ⟨component, _, componentEqual⟩
    rw [inAggregate, ← componentEqual] at equal
    have stemEqual := (SourceName.indexed.inj equal).1
    simp at stemEqual

/-- A splitter structure paired with caller-supplied aggregate naming. -/
@[reducible] def splitterDesignWithNaming (value : Composition.SignalSplitter)
    (aggregateNaming : SignalTypeNaming value.aggregateType) : NamedModule where
  ports := value.ports
  moduleStructure := .splitter value
  naming := splitterWithNaming value aggregateNaming

/-- A combiner structure paired with caller-supplied aggregate naming. -/
@[reducible] def combinerDesignWithNaming (value : Composition.SignalCombiner)
    (aggregateNaming : SignalTypeNaming value.aggregateType) : NamedModule where
  ports := value.ports
  moduleStructure := .combiner value
  naming := combinerWithNaming value aggregateNaming

/-- A splitter structure paired with its default positional naming. -/
@[reducible] def splitterDesign (value : Composition.SignalSplitter) : NamedModule :=
  splitterDesignWithNaming value (.positional value.aggregateType)

/-- A combiner structure paired with its default positional naming. -/
@[reducible] def combinerDesign (value : Composition.SignalCombiner) : NamedModule :=
  combinerDesignWithNaming value (.positional value.aggregateType)

end Silean.Naming.SignalAdapter
