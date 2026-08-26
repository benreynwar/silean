import Silean2.FIRRTL.AdapterNaming
import Silean2.FIRRTL.PrimitiveNaming
import Silean2.FIRRTL.Render
import Silean2.Modules.Register

namespace Silean2.FIRRTL.RegisterNaming

open Silean2 Silean2.FIRRTL

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Register.ports signalType) where
  inputs := ⟨fun | .input => "in"⟩
  outputs := ⟨fun | .output => "out"⟩
  inputTypes := fun | .input => typeNaming
  outputTypes := fun | .output => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.Register.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

private def componentName (splitter : SignalSplitter)
    (component : splitter.ports.outputs.Label) : SourceName :=
  .scoped "register" ((SignalMapNaming.indexed splitter.ports.outputs "component").name component)

def namingWith : (signalType : SignalType) → (typeNaming : SignalTypeNaming signalType) →
    ModuleNaming (Modules.Register.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Register.moduleStructure]
      exact PrimitiveNaming.register
  | .vector length element, typeNaming => by
      rw [Modules.Register.moduleStructure]
      let splitter : SignalSplitter := .vector length element
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split" | .item component => componentName splitter component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item component => namingWith element (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      rw [Modules.Register.moduleStructure]
      let splitter : SignalSplitter := .tuple fields
      exact .composite ⟨"register", "structural", [.shape splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun | .start => "split" | .item component => componentName splitter component
             | .finish => "combine")
        (fun | .start => AdapterNaming.splitterWithNaming splitter typeNaming
             | .item component => namingWith (fields.typeAt component) (typeNaming.component component)
             | .finish => AdapterNaming.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · exact SignalTypes.complexity_typeAt_lt fields component

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

def firrtl (signalType : SignalType) : RenderResult String :=
  renderCircuit (naming signalType)

end Silean2.FIRRTL.RegisterNaming
