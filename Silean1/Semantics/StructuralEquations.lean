import Silean.Foundation.CycleStep
import Silean.Structure.ModuleStructure

namespace Silean

/-! # Simultaneous structural equations

This file gives `ModuleStructure` its contract-independent meaning. A
`HierStep` assigns one cycle's inputs and outputs at every module occurrence
and stores current and next state at stateful leaves. Composite state is
derived from child assignments, matching the hierarchy already determined by
`ModuleStructure`.

`ModuleStructure.IsSolution` requires all leaf and wiring equations to hold
simultaneously. `ModuleStructure.Realizes` hides the complete hierarchy
assignment behind its root boundary `Step`.

Nothing here selects an evaluation order. Existence and complete uniqueness
are separate semantic properties.
-/

abbrev ModuleStructure.State (module : ModuleStructure ports) :=
  module.structuralState.Values

/-- The values visible at the boundary of one structural cycle. -/
abbrev ModuleStructure.Step (module : ModuleStructure ports) :=
  CycleStep ports module.State

/-! ## Leaf equations -/

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

def Composition.SignalSplitter.IsSolution
    (splitter : Composition.SignalSplitter)
    (inputs : splitter.ports.inputs.Values)
    (outputs : splitter.ports.outputs.Values) : Prop :=
  outputs = splitter.outputValues inputs

def Composition.SignalCombiner.IsSolution
    (combiner : Composition.SignalCombiner)
    (inputs : combiner.ports.inputs.Values)
    (outputs : combiner.ports.outputs.Values) : Prop :=
  outputs = combiner.outputValues inputs

/-! ## Signal and wiring evaluation -/

def SignalSource.value (source : SignalSource ports instancePorts signalType)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values) : signalType.Denote :=
  match source with
  | .moduleInput port => inputs port
  | .instanceOutput name port => childOutputs name port

@[simp] theorem SignalSource.value_moduleInput
    {ports : ModulePorts} {instancePorts : InstancePorts}
    (port : ports.inputs.Label)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values) :
    (SignalSource.moduleInput (instancePorts := instancePorts) port).value
      inputs childOutputs = inputs port := rfl

@[simp] theorem SignalSource.value_instanceOutput
    {ports : ModulePorts} {instancePorts : InstancePorts}
    (name : instancePorts.Name)
    (port : (instancePorts.ports name).outputs.Label)
    (inputs : ports.inputs.Values)
    (childOutputs : (child : instancePorts.Name) →
      (instancePorts.ports child).outputs.Values) :
    (SignalSource.instanceOutput (ports := ports) name port).value
      inputs childOutputs = childOutputs name port := rfl

@[simp] theorem EndpointContext.moduleInput_value (context : EndpointContext)
    (port : context.ports.inputs.Label)
    (inputs : context.ports.inputs.Values)
    (childOutputs : (name : context.instancePorts.Name) →
      (context.instancePorts.ports name).outputs.Values) :
    (context.moduleInput port).value inputs childOutputs = inputs port := rfl

@[simp] theorem EndpointContext.instanceOutput_value (context : EndpointContext)
    (name : context.instancePorts.Name)
    (port : (context.instancePorts.ports name).outputs.Label)
    (inputs : context.ports.inputs.Values)
    (childOutputs : (child : context.instancePorts.Name) →
      (context.instancePorts.ports child).outputs.Values) :
    (context.instanceOutput name port).value inputs childOutputs =
      childOutputs name port := rfl

@[simp] theorem SignalSource.value_castType
    {sourceType targetType : SignalType} (equal : sourceType = targetType)
    (source : SignalSource ports instancePorts sourceType)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values) :
    (SignalSource.castType equal source).value inputs childOutputs =
      equal ▸ source.value inputs childOutputs := by
  cases equal
  rfl

/-- Derive one child's complete input values from parent inputs, sibling
outputs, and the composite wiring. -/
@[simp] def Wiring.childInputValues (wiring : Wiring ports instancePorts)
    (inputs : ports.inputs.Values)
    (childOutputs : (name : instancePorts.Name) →
      (instancePorts.ports name).outputs.Values)
    (name : instancePorts.Name) : (instancePorts.ports name).inputs.Values :=
  fun port => (wiring.instanceInput name port).value inputs childOutputs

/-! ## Complete hierarchy assignments -/

/-- The complete cycle assignment for a stateless structural leaf. -/
@[ext] structure CombinationalHierStep (ports : ModulePorts) where
  inputs : ports.inputs.Values
  outputs : ports.outputs.Values

/-- The root boundary assignment and recursive child assignments for a
composite. Current and next state are derived from `children`. -/
@[ext] structure CompositeHierStep (body : ModuleBody)
    (Child : body.instancePorts.Name → Type) where
  inputs : body.ports.inputs.Values
  outputs : body.ports.outputs.Values
  children : (name : body.instancePorts.Name) → Child name

/-- A complete assignment of one cycle's values throughout a hierarchy. -/
def HierStep {ports : ModulePorts} (module : ModuleStructure ports) : Type :=
  match module with
  | .primitive primitive => CycleStep primitive.ports primitive.localState.Values
  | .splitter splitter => CombinationalHierStep splitter.ports
  | .combiner combiner => CombinationalHierStep combiner.ports
  | .composite body childStructure =>
      CompositeHierStep body (fun name => HierStep (childStructure name))
termination_by structural module

namespace HierStep

def inputs {ports : ModulePorts} {module : ModuleStructure ports} :
    HierStep module → ports.inputs.Values :=
  match module with
  | .primitive _ => fun step => CycleStep.inputs step
  | .splitter _ => fun step => CombinationalHierStep.inputs step
  | .combiner _ => fun step => CombinationalHierStep.inputs step
  | .composite _ _ => fun step => CompositeHierStep.inputs step

def outputs {ports : ModulePorts} {module : ModuleStructure ports} :
    HierStep module → ports.outputs.Values :=
  match module with
  | .primitive _ => fun step => CycleStep.outputs step
  | .splitter _ => fun step => CombinationalHierStep.outputs step
  | .combiner _ => fun step => CombinationalHierStep.outputs step
  | .composite _ _ => fun step => CompositeHierStep.outputs step

def currentState {ports : ModulePorts} (module : ModuleStructure ports) :
    HierStep module → module.State :=
  match module with
  | .primitive _ => fun step => CycleStep.currentState step
  | .splitter _ => fun _ => SignalMap.emptyValues
  | .combiner _ => fun _ => SignalMap.emptyValues
  | .composite _ childStructure => fun step name =>
      currentState (childStructure name) (CompositeHierStep.children step name)
termination_by structural module

def nextState {ports : ModulePorts} (module : ModuleStructure ports) :
    HierStep module → module.State :=
  match module with
  | .primitive _ => fun step => CycleStep.nextState step
  | .splitter _ => fun _ => SignalMap.emptyValues
  | .combiner _ => fun _ => SignalMap.emptyValues
  | .composite _ childStructure => fun step name =>
      nextState (childStructure name) (CompositeHierStep.children step name)
termination_by structural module

/-- Project the assignment at the root of a hierarchy. Applying this to a
child assignment gives that child's structural boundary step directly. -/
def step {ports : ModulePorts} {module : ModuleStructure ports}
    (hierStep : HierStep module) : module.Step where
  inputs := hierStep.inputs
  currentState := currentState module hierStep
  outputs := hierStep.outputs
  nextState := nextState module hierStep

@[simp] theorem step_inputs {module : ModuleStructure ports}
    (hierStep : HierStep module) : hierStep.step.inputs = hierStep.inputs := rfl

@[simp] theorem step_outputs {module : ModuleStructure ports}
    (hierStep : HierStep module) : hierStep.step.outputs = hierStep.outputs := rfl

@[simp] theorem step_currentState {module : ModuleStructure ports}
    (hierStep : HierStep module) :
    hierStep.step.currentState = currentState module hierStep := rfl

@[simp] theorem step_nextState {module : ModuleStructure ports}
    (hierStep : HierStep module) :
    hierStep.step.nextState = nextState module hierStep := rfl

def children {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body childStructure))
    (name : body.instancePorts.Name) : HierStep (childStructure name) :=
  CompositeHierStep.children hierStep name

def childInputs {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body childStructure))
    (name : body.instancePorts.Name) :
    (body.instancePorts.ports name).inputs.Values :=
  (hierStep.children name).inputs

def childOutputs {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body childStructure))
    (name : body.instancePorts.Name) :
    (body.instancePorts.ports name).outputs.Values :=
  (hierStep.children name).outputs

/-- Every parent output equals the value at its wired source. -/
def ParentOutputsSatisfy (body : ModuleBody)
    (inputs : body.ports.inputs.Values)
    (outputs : body.ports.outputs.Values)
    (childOutputs : (name : body.instancePorts.Name) →
      (body.instancePorts.ports name).outputs.Values) : Prop :=
  ∀ port, outputs port =
    (body.wiring.moduleOutput port).value inputs childOutputs

/-- Every stored child input equals the value dictated by composite wiring. -/
def ChildInputsSatisfy (body : ModuleBody)
    (inputs : body.ports.inputs.Values)
    (childInputs : (name : body.instancePorts.Name) →
      (body.instancePorts.ports name).inputs.Values)
    (childOutputs : (name : body.instancePorts.Name) →
      (body.instancePorts.ports name).outputs.Values) : Prop :=
  ∀ name, childInputs name =
    body.wiring.childInputValues inputs childOutputs name

/-- Construct a composite assignment once its children have been assigned.
Root outputs are read directly from their wired sources. -/
def compositeFromChildren (body : ModuleBody)
    (childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name))
    (inputs : body.ports.inputs.Values)
    (children : (name : body.instancePorts.Name) →
      HierStep (childStructure name)) :
    HierStep (.composite body childStructure) where
  inputs := inputs
  outputs := fun output =>
    (body.wiring.moduleOutput output).value inputs
      (fun name => (children name).outputs)
  children := children

end HierStep

/-! ## Recursive structural solutions -/

/-- A hierarchy assignment is a solution when all leaf equations and all
composite wiring equations hold simultaneously. -/
def ModuleStructure.IsSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : HierStep module → Prop :=
  match module with
  | ModuleStructure.primitive gate => fun hierStep =>
      gate.IsSolution hierStep.inputs hierStep.currentState
        hierStep.nextState hierStep.outputs
  | ModuleStructure.splitter adapter => fun hierStep =>
      adapter.IsSolution hierStep.inputs hierStep.outputs
  | ModuleStructure.combiner adapter => fun hierStep =>
      adapter.IsSolution hierStep.inputs hierStep.outputs
  | ModuleStructure.composite body childStructure => fun hierStep =>
      HierStep.ParentOutputsSatisfy body hierStep.inputs hierStep.outputs
          hierStep.childOutputs ∧
        HierStep.ChildInputsSatisfy body hierStep.inputs hierStep.childInputs
          hierStep.childOutputs ∧
        ∀ name, (childStructure name).IsSolution (hierStep.children name)
termination_by structural module

/-- A boundary step is realizable when it is the root projection of a complete
satisfying hierarchy assignment. -/
def ModuleStructure.Realizes {ports : ModulePorts}
    (module : ModuleStructure ports) (boundary : module.Step) : Prop :=
  ∃ hierStep, module.IsSolution hierStep ∧ hierStep.step = boundary

namespace ModuleStructure

/-- Extract the defining output equation from a splitter solution. -/
theorem splitter_outputs_of_solution
    {splitter : Composition.SignalSplitter}
    {hierStep : HierStep (.splitter splitter)}
    (solution : (ModuleStructure.splitter splitter).IsSolution hierStep) :
    hierStep.outputs = splitter.outputValues hierStep.inputs :=
  solution

/-- Extract the defining output equation from a combiner solution. -/
theorem combiner_outputs_of_solution
    {combiner : Composition.SignalCombiner}
    {hierStep : HierStep (.combiner combiner)}
    (solution : (ModuleStructure.combiner combiner).IsSolution hierStep) :
    hierStep.outputs = combiner.outputValues hierStep.inputs :=
  solution

/-- Read a parent-output wiring equation pointwise, using the same concrete
child-output projection that appears in a child's boundary step. -/
theorem parent_output {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {hierStep : HierStep (.composite body childStructure)}
    (solution : (ModuleStructure.composite body childStructure).IsSolution hierStep)
    (port : body.ports.outputs.Label) :
    hierStep.outputs port =
      (body.wiring.moduleOutput port).value hierStep.inputs
        (fun child => (hierStep.children child).outputs) :=
  solution.1 port

/-- Read a child-input wiring equation pointwise, in the boundary vocabulary
used by child contracts and realization theorems. -/
theorem child_input {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {hierStep : HierStep (.composite body childStructure)}
    (solution : (ModuleStructure.composite body childStructure).IsSolution hierStep)
    (name : body.instancePorts.Name)
    (port : (body.instancePorts.ports name).inputs.Label) :
    (hierStep.children name).inputs port =
      (body.wiring.instanceInput name port).value hierStep.inputs
        (fun child => (hierStep.children child).outputs) :=
  congrFun (solution.2.1 name) port

theorem realizes_iff_exists_solution {module : ModuleStructure ports}
    {boundary : module.Step} :
    module.Realizes boundary ↔
      ∃ hierStep, module.IsSolution hierStep ∧ hierStep.step = boundary :=
  Iff.rfl

/-- Every satisfying hierarchy assignment realizes its root boundary step. -/
theorem realizes_of_solution {module : ModuleStructure ports}
    {hierStep : HierStep module} (solution : module.IsSolution hierStep) :
    module.Realizes hierStep.step :=
  ⟨hierStep, solution, rfl⟩

/-- Transfer a contract-independent boundary property across an equality of
module structures. This keeps the dependent cast of `Step` internal when a
recursive structure unfolds by a propositional equation rather than by
definitional reduction. -/
theorem boundary_property_of_structure_eq
    {source target : ModuleStructure ports}
    (structureEq : source = target)
    {property : ports.inputs.Values → ports.outputs.Values → Prop}
    (targetCorrect : ∀ {step : target.Step}, target.Realizes step →
      property step.inputs step.outputs)
    {step : source.Step} (realizes : source.Realizes step) :
    property step.inputs step.outputs := by
  subst target
  exact targetCorrect realizes

/-- The selected child of a composite solution is itself a solution. -/
theorem child_isSolution {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {hierStep : HierStep (.composite body childStructure)}
    (solution : (ModuleStructure.composite body childStructure).IsSolution hierStep)
    (name : body.instancePorts.Name) :
    (childStructure name).IsSolution (hierStep.children name) :=
  solution.2.2 name

/-- The selected child step of a composite solution is directly realizable. -/
theorem child_realizes {body : ModuleBody}
    {childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {hierStep : HierStep (.composite body childStructure)}
    (solution : (ModuleStructure.composite body childStructure).IsSolution hierStep)
    (name : body.instancePorts.Name) :
    (childStructure name).Realizes (hierStep.children name).step :=
  realizes_of_solution (child_isSolution solution name)

end ModuleStructure

/-- Consistent immediate-child assignments assemble into a composite
solution. This is the generic final step of structural-existence proofs. -/
theorem HierStep.compositeFromChildren_isSolution (body : ModuleBody)
    (childStructure : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name))
    (inputs : body.ports.inputs.Values)
    (children : (name : body.instancePorts.Name) →
      HierStep (childStructure name))
    (childInputsSatisfy : HierStep.ChildInputsSatisfy body inputs
      (fun name => (children name).inputs)
      (fun name => (children name).outputs))
    (childrenSatisfy : ∀ name,
      (childStructure name).IsSolution (children name)) :
    (ModuleStructure.composite body childStructure).IsSolution
      (HierStep.compositeFromChildren body childStructure inputs children) :=
  ⟨fun _ => rfl, childInputsSatisfy, childrenSatisfy⟩

end Silean
