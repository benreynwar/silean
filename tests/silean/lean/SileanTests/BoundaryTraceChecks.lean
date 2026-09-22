import Silean.Semantics.BoundaryTrace
import Silean.Semantics.StructuralExecution

namespace SileanTests.BoundaryTraceChecks

open Silean

example {ports : ModulePorts} {State : Type}
    (step : CycleStep ports State) :
    step.boundary.inputs = step.inputs ∧
      step.boundary.outputs = step.outputs :=
  ⟨rfl, rfl⟩

example {ports : ModulePorts} {State : Type}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (trace : Trace Step initialState inputValues outputValues finalState) :
    trace.toBoundaryTrace.inputs = inputValues ∧
      trace.toBoundaryTrace.outputs = outputValues :=
  ⟨trace.toBoundaryTrace_inputs, trace.toBoundaryTrace_outputs⟩

example {ports : ModulePorts} {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (execution : module.Executes initialState inputValues outputValues finalState) :
    execution.toBoundaryTrace.length = inputValues.length :=
  execution.toBoundaryTrace_length

end SileanTests.BoundaryTraceChecks
