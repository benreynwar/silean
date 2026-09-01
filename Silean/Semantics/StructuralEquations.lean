import Silean.Structure.ModuleStructure

namespace Silean

/-! # Simultaneous structural equations

This file gives `ModuleStructure` its contract-independent meaning. A
`ProposedValues` value proposes every module output, every instance output, and
all primitive next state. `IsSolution` says that the proposal satisfies all
primitive, adapter, wiring, and child equations simultaneously.

Nothing here selects an evaluation order. A structure can have no solution or
several solutions; existence and uniqueness are separate properties proved by
the dependency and certification layers. -/

abbrev ModuleStructure.State (module : ModuleStructure ports) :=
  module.structuralState.Values

/-! Primitive equations define leaf meaning independently of contracts. -/

def Primitive.OutputsSatisfy (primitive : Primitive)
    (inputs : primitive.ports.inputs.Values)
    (currentState : primitive.localState.Values)
    (outputs : primitive.ports.outputs.Values) : Prop :=
  outputs = primitive.outputValues inputs currentState

def Primitive.NextStateSatisfy (primitive : Primitive)
    (inputs : primitive.ports.inputs.Values)
    (currentState nextState : primitive.localState.Values) : Prop :=
  nextState = primitive.nextStateValues inputs currentState

def Primitive.IsSolution (primitive : Primitive)
    (inputs : primitive.ports.inputs.Values)
    (currentState nextState : primitive.localState.Values)
    (outputs : primitive.ports.outputs.Values) : Prop :=
  primitive.OutputsSatisfy inputs currentState outputs ∧
    primitive.NextStateSatisfy inputs currentState nextState

def Composition.SignalSplitter.IsSolution (splitter : Composition.SignalSplitter)
    (inputs : splitter.ports.inputs.Values)
    (outputs : splitter.ports.outputs.Values) : Prop :=
  outputs = splitter.outputValues inputs

def Composition.SignalCombiner.IsSolution (combiner : Composition.SignalCombiner)
    (inputs : combiner.ports.inputs.Values)
    (outputs : combiner.ports.outputs.Values) : Prop :=
  outputs = combiner.outputValues inputs

/-! A proposal stores one stable output interface at every module occurrence.
Only primitive leaves additionally propose local next state. Composite child
inputs, child current states, and composite next state are derived. -/

structure PrimitiveProposedValues (primitive : Primitive) where
  /-- Proposed current-cycle boundary outputs. -/
  outputs : primitive.ports.outputs.Values
  /-- Proposed primitive state after the next clock edge. -/
  nextState : primitive.localState.Values

def ProposedValues {ports : ModulePorts} (module : ModuleStructure ports) : Type :=
  match module with
  | .primitive primitive => PrimitiveProposedValues primitive
  | .blackbox behavior => PrimitiveProposedValues behavior
  | .splitter splitter => splitter.ports.outputs.Values
  | .combiner combiner => combiner.ports.outputs.Values
  | .composite body childStructure =>
      body.context.ports.outputs.Values ×
        ((name : body.context.instancePorts.Name) → ProposedValues (childStructure name))
termination_by structural module

namespace ProposedValues

def primitive {primitive : Primitive}
    (outputs : primitive.ports.outputs.Values)
    (nextState : primitive.localState.Values) :
    ProposedValues (ModuleStructure.primitive primitive) :=
  ⟨outputs, nextState⟩

def blackbox {behavior : Primitive}
    (outputs : behavior.ports.outputs.Values)
    (nextState : behavior.localState.Values) :
    ProposedValues (ModuleStructure.blackbox behavior) :=
  ⟨outputs, nextState⟩

def splitter {splitter : Composition.SignalSplitter}
    (outputs : splitter.ports.outputs.Values) :
    ProposedValues (ModuleStructure.splitter splitter) :=
  outputs

def combiner {combiner : Composition.SignalCombiner}
    (outputs : combiner.ports.outputs.Values) :
    ProposedValues (ModuleStructure.combiner combiner) :=
  outputs

def composite {body : ModuleBody}
    {childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name)}
    (outputs : body.context.ports.outputs.Values)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name)) :
    ProposedValues (ModuleStructure.composite body childStructure) :=
  ⟨outputs, children⟩

def outputs {ports : ModulePorts} {module : ModuleStructure ports} :
    ProposedValues module → ports.outputs.Values :=
  match module with
  | .primitive _ => fun proposal => PrimitiveProposedValues.outputs proposal
  | .blackbox _ => fun proposal => PrimitiveProposedValues.outputs proposal
  | .splitter _ => fun proposal => proposal
  | .combiner _ => fun proposal => proposal
  | .composite _ _ => fun proposal => proposal.1

def nextStateFor {ports : ModulePorts} (module : ModuleStructure ports) :
    ProposedValues module → module.State :=
  match module with
  | .primitive _ => fun proposal => PrimitiveProposedValues.nextState proposal
  | .blackbox _ => fun proposal => PrimitiveProposedValues.nextState proposal
  | .splitter _ => fun _ => SignalMap.emptyValues
  | .combiner _ => fun _ => SignalMap.emptyValues
  | .composite _ childStructure => fun proposal name =>
      nextStateFor (childStructure name) (proposal.2 name)
termination_by structural module

def nextState {ports : ModulePorts} {module : ModuleStructure ports}
    (proposal : ProposedValues module) : module.State :=
  nextStateFor module proposal

end ProposedValues

def SignalSource.value (source : SignalSource ports instancePorts signalType)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values) : signalType.Denote :=
  match source with
  | .moduleInput port => inputs port
  | .instanceOutput name port => childOutputs name port

/-- Derive one child's complete input values from root inputs, sibling output
values, and the composite wiring. -/
@[simp] def Wiring.childInputValues (wiring : Wiring ports instancePorts)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values)
    (name : instancePorts.Name) : (instancePorts.ports name).inputs.Values :=
  fun port => (wiring.instanceInput name port).value inputs childOutputs

namespace ProposedValues

def childInputs (body : ModuleBody)
    (childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name))
    (inputs : body.context.ports.inputs.Values)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name))
    (name : body.context.instancePorts.Name) :
    (body.context.instancePorts.ports name).inputs.Values :=
  body.wiring.childInputValues inputs
    (fun childName => (children childName).outputs) name

/-- Looking up one induced child input follows exactly that child's wiring
source.  Keeping this application form available prevents proofs from having to
unfold the complete wiring table merely to normalize one port. -/
theorem childInputs_apply (body : ModuleBody)
    (childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name))
    (inputs : body.context.ports.inputs.Values)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name))
    (name : body.context.instancePorts.Name)
    (port : (body.context.instancePorts.ports name).inputs.Label) :
    childInputs body childStructure inputs children name port =
      (body.wiring.instanceInput name port).value inputs
        (fun childName => (children childName).outputs) := rfl

def boundaryOutputsSatisfy (body : ModuleBody)
    (childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name))
    (inputs : body.context.ports.inputs.Values)
    (outputs : body.context.ports.outputs.Values)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name)) : Prop :=
  -- Every parent output equals the value at its wired source.
  ∀ port, outputs port =
    (body.wiring.moduleOutput port).value inputs
      fun name => (children name).outputs

/-- Complete a composite proposal from proposals for all immediate children.
The parent boundary values are not additional proof data: they are read
directly from the sources selected by the wiring. -/
def compositeFromChildren (body : ModuleBody)
    (childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name))
    (inputs : body.context.ports.inputs.Values)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name)) :
    ProposedValues (ModuleStructure.composite body childStructure) :=
  ProposedValues.composite
    (fun output => (body.wiring.moduleOutput output).value inputs
      fun name => (children name).outputs)
    children

def IsSolution {ports : ModulePorts} (module : ModuleStructure ports)
    (proposal : ProposedValues module)
    (inputs : ports.inputs.Values) (currentState : module.State) : Prop :=
  match module with
  | .primitive gate =>
      gate.IsSolution inputs currentState
        (PrimitiveProposedValues.nextState proposal)
        (PrimitiveProposedValues.outputs proposal)
  | .blackbox behavior =>
      behavior.IsSolution inputs currentState
        (PrimitiveProposedValues.nextState proposal)
        (PrimitiveProposedValues.outputs proposal)
  | .splitter splitter => splitter.IsSolution inputs proposal
  | .combiner combiner => combiner.IsSolution inputs proposal
  | .composite body childStructure =>
      -- Boundary wiring and every recursively instantiated child must agree.
      boundaryOutputsSatisfy body childStructure inputs proposal.1 proposal.2 ∧
        ∀ name, IsSolution (childStructure name) (proposal.2 name)
          (childInputs body childStructure inputs proposal.2 name)
          (currentState name)
termination_by structural module

end ProposedValues

def ModuleStructure.IsSolution {ports : ModulePorts} (module : ModuleStructure ports)
    (inputs : ports.inputs.Values) (currentState : module.State)
    (proposal : ProposedValues module) : Prop :=
  ProposedValues.IsSolution module proposal inputs currentState

/-- Consistent immediate-child solutions assemble into a solution of the
composite. This is the generic final step of structural-existence proofs. -/
theorem ProposedValues.compositeFromChildren_isSolution (body : ModuleBody)
    (childStructure : (name : body.context.instancePorts.Name) →
      ModuleStructure (body.context.instancePorts.ports name))
    (inputs : body.context.ports.inputs.Values)
    (currentState : (ModuleStructure.composite body childStructure).State)
    (children : (name : body.context.instancePorts.Name) →
      ProposedValues (childStructure name))
    (childrenSatisfy : ∀ name,
      (childStructure name).IsSolution
        (ProposedValues.childInputs body childStructure inputs children name)
        (currentState name) (children name)) :
    (ModuleStructure.composite body childStructure).IsSolution inputs currentState
      (ProposedValues.compositeFromChildren body childStructure inputs children) := by
  constructor
  · intro output
    rfl
  · exact childrenSatisfy

end Silean
