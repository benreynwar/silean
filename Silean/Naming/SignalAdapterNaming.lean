import Silean.Naming.ModuleNaming

namespace Silean.Naming.SignalAdapter

open Silean Silean.Composition Silean.Naming

def splitterPortsWithNaming : (splitter : Composition.SignalSplitter) →
    SignalTypeNaming splitter.aggregateType → ModulePortsNaming splitter.ports
  | .vector length element, aggregateNaming =>
      { inputs := .indexed (aggregateSignalMap (.vector length element)) "aggregate"
        outputs := .indexed (SignalType.vectorComponents length element) "component"
        inputTypes := fun | .value => aggregateNaming
        outputTypes := fun component => aggregateNaming.component component }
  | .tuple fields, aggregateNaming =>
      { inputs := .indexed (aggregateSignalMap (.tuple fields)) "aggregate"
        outputs := .indexed fields.componentMap "component"
        inputTypes := fun | .value => aggregateNaming
        outputTypes := fun component => aggregateNaming.component component }

def combinerPortsWithNaming : (combiner : Composition.SignalCombiner) →
    SignalTypeNaming combiner.aggregateType → ModulePortsNaming combiner.ports
  | .vector length element, aggregateNaming =>
      { inputs := .indexed (SignalType.vectorComponents length element) "component"
        outputs := .indexed (aggregateSignalMap (.vector length element)) "aggregate"
        inputTypes := fun component => aggregateNaming.component component
        outputTypes := fun | .value => aggregateNaming }
  | .tuple fields, aggregateNaming =>
      { inputs := .indexed fields.componentMap "component"
        outputs := .indexed (aggregateSignalMap (.tuple fields)) "aggregate"
        inputTypes := fun component => aggregateNaming.component component
        outputTypes := fun | .value => aggregateNaming }

def splitterPorts (splitter : Composition.SignalSplitter) : ModulePortsNaming splitter.ports :=
  splitterPortsWithNaming splitter (.positional splitter.aggregateType)

def combinerPorts (combiner : Composition.SignalCombiner) : ModulePortsNaming combiner.ports :=
  combinerPortsWithNaming combiner (.positional combiner.aggregateType)

def splitterWithNaming (value : Composition.SignalSplitter)
    (aggregateNaming : SignalTypeNaming value.aggregateType) :
    ModuleNaming (.splitter value) :=
  .splitter value ⟨"split", "aggregate", [.shape value.aggregateType]⟩
    (splitterPortsWithNaming value aggregateNaming)

def combinerWithNaming (value : Composition.SignalCombiner)
    (aggregateNaming : SignalTypeNaming value.aggregateType) :
    ModuleNaming (.combiner value) :=
  .combiner value ⟨"combine", "aggregate", [.shape value.aggregateType]⟩
    (combinerPortsWithNaming value aggregateNaming)

def splitter (value : Composition.SignalSplitter) : ModuleNaming (.splitter value) :=
  splitterWithNaming value (.positional value.aggregateType)

def combiner (value : Composition.SignalCombiner) : ModuleNaming (.combiner value) :=
  combinerWithNaming value (.positional value.aggregateType)

end Silean.Naming.SignalAdapter
