import Silean.Primitive
import Silean.SignalAdapter
import Silean.Structure.ModuleBody

namespace Silean

/-! A complete reusable module definition. A composite owns one correctly
typed child module definition for every named instance in its body. Reusing the
same child value for several names shares a definition; following names during
recursive traversal distinguishes hardware occurrences. -/

inductive ModuleStructure : ModulePorts → Type 1
  | primitive (primitive : Primitive) : ModuleStructure primitive.ports
  | splitter (splitter : SignalSplitter) : ModuleStructure splitter.ports
  | combiner (combiner : SignalCombiner) : ModuleStructure combiner.ports
  | composite (body : ModuleBody)
      (childStructure : (name : body.context.instances.Name) →
        ModuleStructure (body.context.instances.ports name)) :
      ModuleStructure body.context.ports

/-! Structural state is obtained from the complete module definition. A
composite branch is labelled by its instance names and recursively contains
the state of the actual child module attached at each name. -/

def ModuleStructure.structuralState (module : ModuleStructure ports) : StructuralState :=
  match module with
  | .primitive gate => .local gate.localState
  | .splitter _ => .local emptySignalMap
  | .combiner _ => .local emptySignalMap
  | .composite body childStructure =>
      .children body.context.instances.Name body.context.instances.names
        fun name => (childStructure name).structuralState

end Silean
