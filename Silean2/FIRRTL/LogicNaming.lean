import Silean2.FIRRTL.AdapterNaming
import Silean2.FIRRTL.PrimitiveNaming
import Silean2.Modules.Mask
import Silean2.Modules.BitwiseOr

namespace Silean2.FIRRTL

open Silean2

private def indexedComponent (signals : SignalMap) (scope : String)
    (component : signals.Label) : SourceName :=
  .scoped scope ((SignalMapNaming.indexed signals "component").name component)

namespace MaskNaming

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Mask.ports signalType) where
  inputs := ⟨fun | .value => "value" | .mask => "mask"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => typeNaming | .mask => .bit
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.Mask.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Mask.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Mask.moduleStructure]
      unfold Modules.Mask.bitModuleStructure Certified.moduleStructure
      exact .composite ⟨"mask", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => PrimitiveNaming.and)
  | .vector length element, typeNaming => by
      rw [Modules.Mask.moduleStructure]
      let splitter : SignalSplitter := .vector length element
      exact .composite ⟨"mask", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split" | .item component => indexedComponent splitter.ports.outputs "mask" component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item component => namingWith element (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.Mask.moduleStructure]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨"mask", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split" | .item component => indexedComponent splitter.ports.outputs "mask" component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item component => namingWith (fields.typeAt component) (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) : ModuleNaming (Modules.Mask.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end MaskNaming

namespace BitwiseOrNaming

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.BitwiseOr.ports signalType) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .left | .right => typeNaming
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.BitwiseOr.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.BitwiseOr.moduleStructure]
      unfold Modules.BitwiseOr.bitModuleStructure Certified.moduleStructure
      exact .composite ⟨"bitwise_or", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => PrimitiveNaming.or)
  | .vector length element, typeNaming => by
      rw [Modules.BitwiseOr.moduleStructure]
      let splitter : SignalSplitter := .vector length element
      exact .composite ⟨"bitwise_or", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split_left"
             | .item (.inl _) => "split_right"
             | .item (.inr component) => indexedComponent splitter.ports.outputs "or" component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item (.inl _) => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item (.inr component) => namingWith element (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.BitwiseOr.moduleStructure]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨"bitwise_or", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split_left"
             | .item (.inl _) => "split_right"
             | .item (.inr component) => indexedComponent splitter.ports.outputs "or" component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item (.inl _) => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item (.inr component) =>
                 namingWith (fields.typeAt component) (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end BitwiseOrNaming

end Silean2.FIRRTL
