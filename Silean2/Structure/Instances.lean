import Silean2.Foundation.ModulePorts

namespace Silean2

/-! A canonically ordered collection of symbolic module instances. Each
instance records the exact interface required from its recursively owned child
definition; the child `ModuleStructure` itself is attached by the hierarchy layer. -/

abbrev Instances := EnumeratedMap ModulePorts

abbrev Instances.Name (instances : Instances) := instances.Key

abbrev Instances.names (instances : Instances) := instances.keys

abbrev Instances.ports (instances : Instances) := instances.value

end Silean2
