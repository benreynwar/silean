import Silean.Semantics.StructuralObservation

namespace SileanTests.StructuralObservationChecks

open Silean

example {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (execution : module.Executes initialState inputs outputs finalState) :
    ∃ hierarchy,
      module.ObservedExecutes initialState inputs hierarchy finalState ∧
      hierarchy.map HierStep.outputs = outputs :=
  execution.observe

example {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {initialState finalState :
      (ModuleStructure.composite body children).State}
    {inputs : List body.ports.inputs.Values}
    {hierarchy : List
      (HierStep (ModuleStructure.composite body children))}
    (execution : (ModuleStructure.composite body children).ObservedExecutes
      initialState inputs hierarchy finalState)
    (name : body.instancePorts.Name) :
    (children name).Executes (initialState name)
      (hierarchy.map fun step => (step.children name).inputs)
      (hierarchy.map fun step => (step.children name).outputs)
      (finalState name) :=
  execution.child name

end SileanTests.StructuralObservationChecks
