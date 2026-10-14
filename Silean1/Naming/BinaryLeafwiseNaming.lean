import Silean.Composition.BinaryLeafwise
import Silean.Naming.SignalAdapterNaming

namespace Silean.Naming.BinaryLeafwise

open Silean Silean.Composition Silean.Composition.BinaryLeafwise

variable [operation : Operation] [gate : BitGate operation]

private def indexedComponent (scope : String)
    (signals : SignalMap) (component : signals.Label) : SourceName :=
  .scoped scope ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (BinaryLeafwise.ports signalType) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .left | .right => typeNaming
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (BinaryLeafwise.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

/-- Recursively name a binary leafwise hierarchy. Concrete module and
primitive names remain arguments supplied by the module file. -/
def namingWith (moduleName componentScope : String)
    (bitNaming : ModuleNaming gate.certified.moduleStructure) :
    (signalType : SignalType) → SignalTypeNaming signalType →
      ModuleNaming (BinaryLeafwise.moduleStructure signalType)
  | .bit, _ => by
      rw [BinaryLeafwise.moduleStructure,
        LeafwiseInterface.moduleStructure.eq_1]
      unfold BinaryLeafwise.bitModuleStructure
      exact .composite ⟨moduleName, "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => bitNaming)
  | .vector length elementType, typeNaming => by
      rw [BinaryLeafwise.moduleStructure,
        LeafwiseInterface.moduleStructure.eq_2]
      let splitter : SignalSplitter := .vector length elementType
      exact .composite ⟨moduleName, "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .left => "split_left"
          | .splitter .right => "split_right"
          | .component component =>
              .scoped componentScope (.indexed "component" component.val)
          | .combiner .result => "combine")
        (fun
          | .splitter .left =>
              SignalAdapter.splitterWithNaming splitter typeNaming
          | .splitter .right =>
              SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingWith moduleName componentScope bitNaming elementType
                (typeNaming.component component)
          | .combiner .result =>
              SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [BinaryLeafwise.moduleStructure,
        LeafwiseInterface.moduleStructure.eq_3]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨moduleName, "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .left => "split_left"
          | .splitter .right => "split_right"
          | .component component =>
              indexedComponent componentScope splitter.ports.outputs component
          | .combiner .result => "combine")
        (fun
          | .splitter .left =>
              SignalAdapter.splitterWithNaming splitter typeNaming
          | .splitter .right =>
              SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingWith moduleName componentScope bitNaming
                (fields.typeAt component) (typeNaming.component component)
          | .combiner .result =>
              SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

def naming (moduleName componentScope : String)
    (bitNaming : ModuleNaming gate.certified.moduleStructure)
    (signalType : SignalType) :
    ModuleNaming (BinaryLeafwise.moduleStructure signalType) :=
  namingWith moduleName componentScope bitNaming signalType (.positional signalType)

end Silean.Naming.BinaryLeafwise
