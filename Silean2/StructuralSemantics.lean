import Silean2.Structure.ModuleStructure

namespace Silean2

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

def SignalSplitter.IsSolution (splitter : SignalSplitter)
    (inputs : splitter.ports.inputs.Values)
    (outputs : splitter.ports.outputs.Values) : Prop :=
  outputs = splitter.outputValues inputs

def SignalCombiner.IsSolution (combiner : SignalCombiner)
    (inputs : combiner.ports.inputs.Values)
    (outputs : combiner.ports.outputs.Values) : Prop :=
  outputs = combiner.outputValues inputs

/-! A proposal stores one stable output interface at every module occurrence.
Only primitive leaves additionally propose local next state. Composite child
inputs, child current states, and composite next state are derived. -/

structure PrimitiveProposedValues (primitive : Primitive) where
  outputs : primitive.ports.outputs.Values
  nextState : primitive.localState.Values

def ProposedValues {ports : ModulePorts} (module : ModuleStructure ports) : Type :=
  match module with
  | .primitive primitive => PrimitiveProposedValues primitive
  | .splitter splitter => splitter.ports.outputs.Values
  | .combiner combiner => combiner.ports.outputs.Values
  | .composite body childStructure =>
      body.context.ports.outputs.Values ×
        ((name : body.context.instances.Name) → ProposedValues (childStructure name))
termination_by structural module

namespace ProposedValues

def primitive {primitive : Primitive}
    (outputs : primitive.ports.outputs.Values)
    (nextState : primitive.localState.Values) :
    ProposedValues (ModuleStructure.primitive primitive) :=
  ⟨outputs, nextState⟩

def splitter {splitter : SignalSplitter}
    (outputs : splitter.ports.outputs.Values) :
    ProposedValues (ModuleStructure.splitter splitter) :=
  outputs

def combiner {combiner : SignalCombiner}
    (outputs : combiner.ports.outputs.Values) :
    ProposedValues (ModuleStructure.combiner combiner) :=
  outputs

def composite {body : ModuleBody}
    {childStructure : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (outputs : body.context.ports.outputs.Values)
    (children : (name : body.context.instances.Name) →
      ProposedValues (childStructure name)) :
    ProposedValues (ModuleStructure.composite body childStructure) :=
  ⟨outputs, children⟩

def outputs {ports : ModulePorts} {module : ModuleStructure ports} :
    ProposedValues module → ports.outputs.Values :=
  match module with
  | .primitive _ => fun proposal => PrimitiveProposedValues.outputs proposal
  | .splitter _ => fun proposal => proposal
  | .combiner _ => fun proposal => proposal
  | .composite _ _ => fun proposal => proposal.1

def nextStateFor {ports : ModulePorts} (module : ModuleStructure ports) :
    ProposedValues module → module.State :=
  match module with
  | .primitive _ => fun proposal => PrimitiveProposedValues.nextState proposal
  | .splitter _ => fun _ => SignalMap.emptyValues
  | .combiner _ => fun _ => SignalMap.emptyValues
  | .composite _ childStructure => fun proposal name =>
      nextStateFor (childStructure name) (proposal.2 name)
termination_by structural module

def nextState {ports : ModulePorts} {module : ModuleStructure ports}
    (proposal : ProposedValues module) : module.State :=
  nextStateFor module proposal

end ProposedValues

def SignalSource.value (source : SignalSource ports instances signalType)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instances.Name) →
      (instances.ports name).outputs.Values) : signalType.Denote :=
  match source with
  | .moduleInput port => inputs port
  | .instanceOutput name port => childOutputs name port

namespace ProposedValues

def childInputs (body : ModuleBody)
    (childStructure : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name))
    (inputs : body.context.ports.inputs.Values)
    (children : (name : body.context.instances.Name) →
      ProposedValues (childStructure name))
    (name : body.context.instances.Name) :
    (body.context.instances.ports name).inputs.Values :=
  fun port =>
    (body.wiring.instanceInput name port).value inputs
      fun childName => (children childName).outputs

def boundaryOutputsSatisfy (body : ModuleBody)
    (childStructure : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name))
    (inputs : body.context.ports.inputs.Values)
    (outputs : body.context.ports.outputs.Values)
    (children : (name : body.context.instances.Name) →
      ProposedValues (childStructure name)) : Prop :=
  ∀ port, outputs port =
    (body.wiring.moduleOutput port).value inputs
      fun name => (children name).outputs

def IsSolution {ports : ModulePorts} (module : ModuleStructure ports)
    (proposal : ProposedValues module)
    (inputs : ports.inputs.Values) (currentState : module.State) : Prop :=
  match module with
  | .primitive gate =>
      gate.IsSolution inputs currentState
        (PrimitiveProposedValues.nextState proposal)
        (PrimitiveProposedValues.outputs proposal)
  | .splitter splitter => splitter.IsSolution inputs proposal
  | .combiner combiner => combiner.IsSolution inputs proposal
  | .composite body childStructure =>
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

end Silean2
