import Silean.Structure.Primitive
import Silean.Composition.SignalAdapter
import Silean.Structure.ModuleBody

namespace Silean

/-! # Hardware hierarchy

`ModuleStructure` is the complete structural description consumed by
structural semantics, naming, and FIRRTL generation. It contains no behavioral
contract and no evaluation schedule.

A composite gives one level of typed wiring and assigns a structure to every
named instance. Reusing the same child definition at several names creates
several hardware instances. Primitive and signal-adapter leaves terminate the
hierarchy.

The wiring denotes simultaneous equations rather than an execution order.
`StructuralEquations` defines what it means for proposed wire values to solve
those equations; separate existence and uniqueness proofs establish that the
structure has one well-defined result. -/

inductive ModuleStructure : ModulePorts → Type 1
  /-- A leaf implemented by a primitive. -/
  | primitive (primitive : Primitive) : ModuleStructure primitive.ports
  /-- A leaf that separates an aggregate signal into its components. -/
  | splitter (splitter : Composition.SignalSplitter) : ModuleStructure splitter.ports
  /-- A leaf that joins component signals into an aggregate signal. -/
  | combiner (combiner : Composition.SignalCombiner) : ModuleStructure combiner.ports
  /-- One level of child interfaces and wiring, together with a structural
  implementation for every child instance. -/
  | composite (body : ModuleBody)
      (childStructure : (name : body.context.instancePorts.Name) →
        ModuleStructure (body.context.instancePorts.ports name)) :
      ModuleStructure body.context.ports

/-! Structural state is obtained from the complete module definition. A
composite branch is labelled by its instance names and recursively contains
the state of the actual child module attached at each name. -/

def ModuleStructure.structuralState (module : ModuleStructure ports) : StructuralState :=
  match module with
  | .primitive gate => .leaf gate.localState
  | .splitter _ => .leaf emptySignalMap
  | .combiner _ => .leaf emptySignalMap
  | .composite body childStructure =>
      .children
        { Key := body.context.instancePorts.Name
          keys := body.context.instancePorts.names
          value := fun name => (childStructure name).structuralState }

end Silean
