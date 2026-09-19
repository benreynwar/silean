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

/-- Recursive binary-leafwise naming preserves the boundary naming supplied
for the aggregate type. Clients should use this theorem instead of unfolding
the recursive structure and its equality transports. -/
theorem namingWith_ports (moduleName componentScope : String)
    (bitNaming : ModuleNaming gate.certified.moduleStructure)
    (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    (namingWith moduleName componentScope bitNaming signalType typeNaming).ports =
      portsWithNaming signalType typeNaming := by
  cases signalType with
  | bit =>
      rw [namingWith.eq_1]
      erw [ModuleNaming.ports_mpr_of_eq
        (BinaryLeafwise.moduleStructure.eq_1 .bit)]
      erw [ModuleNaming.ports_mpr_of_eq
        (LeafwiseInterface.moduleStructure.eq_1
          BinaryLeafwise.interface BinaryLeafwise.bitModuleStructure)]
      cases typeNaming
      rfl
  | vector length elementType =>
      rw [namingWith.eq_2]
      erw [ModuleNaming.ports_mpr_of_eq
        (BinaryLeafwise.moduleStructure.eq_1 (.vector length elementType))]
      erw [ModuleNaming.ports_mpr_of_eq
        (LeafwiseInterface.moduleStructure.eq_2
          BinaryLeafwise.interface BinaryLeafwise.bitModuleStructure
          length elementType)]
      rfl
  | tuple fields =>
      rw [namingWith.eq_3]
      erw [ModuleNaming.ports_mpr_of_eq
        (BinaryLeafwise.moduleStructure.eq_1 (.tuple fields))]
      erw [ModuleNaming.ports_mpr_of_eq
        (LeafwiseInterface.moduleStructure.eq_3
          BinaryLeafwise.interface BinaryLeafwise.bitModuleStructure fields)]
      rfl

end Silean.Naming.BinaryLeafwise
