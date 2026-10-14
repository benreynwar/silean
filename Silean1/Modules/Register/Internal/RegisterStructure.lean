import Silean.Modules.Register.Register
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Register

open Silean

/-! ## Hardware structure

A bit is one register primitive. A vector or tuple is split into its immediate
components, registered recursively, and recombined with the same shape. -/

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  interface.moduleStructure (.primitive Primitives.register) signalType

end Silean.Modules.Register

namespace Silean.Modules.Register.Naming

open Silean Silean.Naming

/-! ## Emission naming -/

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Register.ports signalType) where
  inputs := ⟨fun | .input => "in"⟩
  outputs := ⟨fun | .output => "out"⟩
  inputTypes := fun | .input => typeNaming
  outputTypes := fun | .output => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Register.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

private def componentName (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) : SourceName :=
  .scoped "register"
    ((SignalMapNaming.indexed splitter.ports.outputs "component").name component)

private def namingForType : (signalType : SignalType) → SignalTypeNaming signalType →
      ModuleNaming (Modules.Register.moduleStructure signalType)
  | .bit, _ => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_1]
      exact Silean.Naming.Primitive.register
  | .vector length elementType, typeNaming => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_2]
      let splitter : Composition.SignalSplitter := .vector length elementType
      exact .composite ⟨"register", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => .scoped "register" (.indexed "component" component.val)
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingForType elementType (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_3]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"register", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => componentName splitter component
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component => by
              exact namingForType (fields.typeAt component)
                (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  namingForType signalType (.positional signalType)

/-- Apply authored names only to the emitted register boundary. Recursive
splitters, combiners, and component registers retain canonical positional
naming. -/
def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  (naming signalType).withPorts (portsWithNaming signalType typeNaming)

end Silean.Modules.Register.Naming

namespace Silean.Modules.Register

/-! ## Complete designs -/

/-- The canonical register structure paired with caller-supplied emitted names. -/
def designWith {signalType : SignalType}
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType
  naming := Naming.namingWith signalType typeNaming

/-- The generic register structure paired with its default recursive naming. -/
def design (signalType : SignalType) : Silean.Naming.NamedModule :=
  designWith (Naming.SignalTypeNaming.positional signalType)


end Silean.Modules.Register
