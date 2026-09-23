import Silean.Semantics.StructuralExecution
import Silean.Semantics.ModuleBodyTrace

namespace Silean

/-! # Observing structural executions

`ModuleStructure.Executes` intentionally hides each satisfying hierarchy
assignment. Multi-child temporal proofs sometimes need those assignments back
in one synchronized sequence. `ObservedExecutes` retains them without changing
the underlying structural transition semantics, and permits any immediate
child execution to be projected from that same sequence.
-/

/-- One structural transition together with its complete satisfying hierarchy
assignment. -/
def ModuleStructure.ObservedTransition (module : ModuleStructure ports)
    (inputs : ports.inputs.Values) (currentState : module.State)
    (hierStep : HierStep module) (nextState : module.State) : Prop :=
  module.IsSolution hierStep ∧
    hierStep.inputs = inputs ∧
    HierStep.currentState module hierStep = currentState ∧
    HierStep.nextState module hierStep = nextState

/-- A structural execution whose observation at each cycle is the complete
satisfying hierarchy assignment. -/
abbrev ModuleStructure.ObservedExecutes (module : ModuleStructure ports) :=
  Trace module.ObservedTransition

namespace HierStep

/-- Erase one hierarchy assignment to its state-free root boundary. -/
def boundaryStep {module : ModuleStructure ports}
    (hierStep : HierStep module) : BoundaryStep ports where
  inputs := hierStep.inputs
  outputs := hierStep.outputs

@[simp] theorem boundaryStep_inputs {module : ModuleStructure ports}
    (hierStep : HierStep module) :
    hierStep.boundaryStep.inputs = hierStep.inputs :=
  rfl

@[simp] theorem boundaryStep_outputs {module : ModuleStructure ports}
    (hierStep : HierStep module) :
    hierStep.boundaryStep.outputs = hierStep.outputs :=
  rfl

/-- Erase a concrete composite hierarchy assignment to the parent and
immediate-child boundaries of its permanent `ModuleBody`. -/
def toBodyStep {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body children)) : body.Step where
  parent := hierStep.boundaryStep
  child := fun name => (hierStep.children name).boundaryStep

@[simp] theorem toBodyStep_parent {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body children)) :
    hierStep.toBodyStep.parent = hierStep.boundaryStep :=
  rfl

@[simp] theorem toBodyStep_child {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierStep : HierStep (.composite body children))
    (name : body.instancePorts.Name) :
    hierStep.toBodyStep.child name =
      (hierStep.children name).boundaryStep :=
  rfl

/-- A concrete composite solution obeys the same body-wiring relation used by
implementation-independent top-down proofs. -/
theorem toBodyStep_wiringHolds {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {hierStep : HierStep (.composite body children)}
    (solution : (ModuleStructure.composite body children).IsSolution
      hierStep) :
    hierStep.toBodyStep.WiringHolds := by
  constructor
  · funext output
    exact solution.1 output
  · intro name
    exact solution.2.1 name

end HierStep

namespace ModuleBody.Trace

/-- Erase a synchronized list of concrete composite hierarchy assignments to
an implementation-independent trace of their common body. -/
def ofHierarchy {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children))) : body.Trace :=
  hierarchy.map HierStep.toBodyStep

@[simp] theorem ofHierarchy_parent {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children))) :
    (ofHierarchy hierarchy).parent = hierarchy.map HierStep.boundaryStep := by
  simp [ofHierarchy, parent]

@[simp] theorem ofHierarchy_child {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children)))
    (name : body.instancePorts.Name) :
    (ofHierarchy hierarchy).child name =
      hierarchy.map fun step => (step.children name).boundaryStep := by
  simp [ofHierarchy, child]

@[simp] theorem ofHierarchy_parent_inputs {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children))) :
    (ofHierarchy hierarchy).parent.inputs =
      hierarchy.map HierStep.inputs := by
  simp [ofHierarchy, ModuleBody.Trace.parent, BoundaryTrace.inputs,
    HierStep.toBodyStep, HierStep.boundaryStep]

@[simp] theorem ofHierarchy_parent_outputs {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children))) :
    (ofHierarchy hierarchy).parent.outputs =
      hierarchy.map HierStep.outputs := by
  simp [ofHierarchy, ModuleBody.Trace.parent, BoundaryTrace.outputs,
    HierStep.toBodyStep, HierStep.boundaryStep]

@[simp] theorem ofHierarchy_child_inputs {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children)))
    (name : body.instancePorts.Name) :
    ((ofHierarchy hierarchy).child name).inputs =
      hierarchy.map fun step => (step.children name).inputs := by
  simp [ofHierarchy, ModuleBody.Trace.child, BoundaryTrace.inputs,
    HierStep.toBodyStep, HierStep.boundaryStep]

@[simp] theorem ofHierarchy_child_outputs {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (hierarchy : List (HierStep (.composite body children)))
    (name : body.instancePorts.Name) :
    ((ofHierarchy hierarchy).child name).outputs =
      hierarchy.map fun step => (step.children name).outputs := by
  simp [ofHierarchy, ModuleBody.Trace.child, BoundaryTrace.outputs,
    HierStep.toBodyStep, HierStep.boundaryStep]

end ModuleBody.Trace

namespace ModuleStructure

/-- Recover one synchronized hierarchy-step sequence from an ordinary
structural execution. -/
theorem Executes.observe
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (execution : module.Executes initialState inputs outputs finalState) :
    ∃ hierarchy,
      module.ObservedExecutes initialState inputs hierarchy finalState ∧
      hierarchy.map HierStep.outputs = outputs := by
  induction execution with
  | nil =>
      exact ⟨[], .nil _, rfl⟩
  | @cons currentState nextState finalState remainingInputs remainingOutputs
      input output transition rest induction =>
      rcases transition with ⟨hierStep, solution, rootEqual⟩
      rcases induction with ⟨hierarchy, observedRest, outputsEqual⟩
      have inputEqual : hierStep.inputs = input :=
        congrArg CycleStep.inputs rootEqual
      have outputEqual : hierStep.outputs = output :=
        congrArg CycleStep.outputs rootEqual
      have currentStateEqual :
          HierStep.currentState module hierStep = currentState :=
        congrArg CycleStep.currentState rootEqual
      have nextStateEqual :
          HierStep.nextState module hierStep = nextState :=
        congrArg CycleStep.nextState rootEqual
      refine ⟨hierStep :: hierarchy,
        .cons input hierStep ?_ observedRest, ?_⟩
      · exact ⟨solution, inputEqual, currentStateEqual, nextStateEqual⟩
      · simp [outputEqual, outputsEqual]

/-- Every retained hierarchy assignment satisfies the structural equations. -/
theorem ObservedExecutes.solution_of_mem
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {hierarchy : List (HierStep module)}
    (execution :
      module.ObservedExecutes initialState inputs hierarchy finalState) :
    ∀ hierStep ∈ hierarchy, module.IsSolution hierStep := by
  induction execution with
  | nil => simp
  | cons _ hierStep transition _ induction =>
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact transition.1
      · exact induction candidate later

/-- The retained hierarchy inputs are exactly the original parent input
sequence. -/
theorem ObservedExecutes.hierarchy_inputs
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {hierarchy : List (HierStep module)}
    (execution :
      module.ObservedExecutes initialState inputs hierarchy finalState) :
    hierarchy.map HierStep.inputs = inputs := by
  induction execution with
  | nil => rfl
  | cons _ _ transition _ induction =>
      simp [transition.2.1, induction]

/-- Read the original parent input at one observed hierarchy position. -/
theorem ObservedExecutes.input_at
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {hierarchy : List (HierStep module)}
    (execution :
      module.ObservedExecutes initialState inputs hierarchy finalState)
    (t : Nat) (hierarchyInTrace : t < hierarchy.length)
    (inputInTrace : t < inputs.length) :
    (hierarchy.get ⟨t, hierarchyInTrace⟩).inputs =
      inputs.get ⟨t, inputInTrace⟩ := by
  have atPosition := congrArg (fun values => values[t]?)
    execution.hierarchy_inputs
  rw [List.getElem?_map,
    List.getElem?_eq_getElem hierarchyInTrace,
    List.getElem?_eq_getElem inputInTrace] at atPosition
  simpa using atPosition

/-- Read the original parent output at one observed hierarchy position. -/
theorem ObservedExecutes.output_at
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    {hierarchy : List (HierStep module)}
    (_execution :
      module.ObservedExecutes initialState inputs hierarchy finalState)
    (outputsEqual : hierarchy.map HierStep.outputs = outputs)
    (t : Nat) (hierarchyInTrace : t < hierarchy.length)
    (outputInTrace : t < outputs.length) :
    (hierarchy.get ⟨t, hierarchyInTrace⟩).outputs =
      outputs.get ⟨t, outputInTrace⟩ := by
  have atPosition := congrArg (fun values => values[t]?) outputsEqual
  rw [List.getElem?_map,
    List.getElem?_eq_getElem hierarchyInTrace,
    List.getElem?_eq_getElem outputInTrace] at atPosition
  simpa using atPosition

/-- The hierarchy assignment at every observed position is a structural
solution. -/
theorem ObservedExecutes.solution_at
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {inputs : List ports.inputs.Values}
    {hierarchy : List (HierStep module)}
    (execution :
      module.ObservedExecutes initialState inputs hierarchy finalState)
    (t : Nat) (hierarchyInTrace : t < hierarchy.length) :
    module.IsSolution (hierarchy.get ⟨t, hierarchyInTrace⟩) :=
  execution.solution_of_mem _
    (List.get_mem hierarchy ⟨t, hierarchyInTrace⟩)

/-- Project any immediate child execution from a synchronized observed parent
execution. All projected children therefore retain the same cycle indexing. -/
theorem ObservedExecutes.child
    {body : ModuleBody}
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
      (finalState name) := by
  induction execution with
  | nil =>
      exact .nil _
  | @cons currentState nextState finalState remainingInputs remainingHierarchy
      input hierStep transition rest induction =>
      have childTransition := transition_of_solution
        (child_isSolution transition.1 name)
      have currentStateEqual := congrFun transition.2.2.1 name
      have nextStateEqual := congrFun transition.2.2.2 name
      change HierStep.currentState (children name)
        (hierStep.children name) = currentState name at currentStateEqual
      change HierStep.nextState (children name)
        (hierStep.children name) = nextState name at nextStateEqual
      rw [currentStateEqual, nextStateEqual] at childTransition
      exact .cons (hierStep.children name).inputs
        (hierStep.children name).outputs childTransition induction

/-- Erasing an observed concrete composite execution produces a body trace
whose bundled boundaries obey the permanent body wiring. -/
theorem ObservedExecutes.bodyTrace_wiringHolds
    {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {initialState finalState :
      (ModuleStructure.composite body children).State}
    {inputs : List body.ports.inputs.Values}
    {hierarchy : List
      (HierStep (ModuleStructure.composite body children))}
    (execution : (ModuleStructure.composite body children).ObservedExecutes
      initialState inputs hierarchy finalState) :
    (ModuleBody.Trace.ofHierarchy hierarchy).WiringHolds := by
  intro bodyStep member
  rcases List.mem_map.mp member with ⟨hierStep, hierarchyMember, rfl⟩
  exact HierStep.toBodyStep_wiringHolds
    (execution.solution_of_mem hierStep hierarchyMember)

/-- The child trace projected from a body trace is exactly the boundary trace
of the concrete child execution projected from the same observed parent
execution. -/
theorem ObservedExecutes.child_toBoundaryTrace
    {body : ModuleBody}
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
    (execution.child name).toBoundaryTrace =
      (ModuleBody.Trace.ofHierarchy hierarchy).child name := by
  apply BoundaryTrace.ext
  · rw [Trace.toBoundaryTrace_inputs]
    exact (ModuleBody.Trace.ofHierarchy_child_inputs hierarchy name).symm
  · rw [Trace.toBoundaryTrace_outputs]
    exact (ModuleBody.Trace.ofHierarchy_child_outputs hierarchy name).symm

/-- A concrete composite execution supplies exactly the artifact consumed by
a top-down body theorem: a wiring-valid body trace with the same parent
boundary trace and a concrete execution behind every child projection. -/
theorem Executes.toBodyTrace
    {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    {initialState finalState :
      (ModuleStructure.composite body children).State}
    {inputs : List body.ports.inputs.Values}
    {outputs : List body.ports.outputs.Values}
    (execution : (ModuleStructure.composite body children).Executes
      initialState inputs outputs finalState) :
    ∃ bodyTrace : body.Trace,
      bodyTrace.WiringHolds ∧
      bodyTrace.parent = execution.toBoundaryTrace ∧
      ∀ name,
        ∃ childExecution : (children name).Executes (initialState name)
            (bodyTrace.child name).inputs (bodyTrace.child name).outputs
            (finalState name),
          childExecution.toBoundaryTrace = bodyTrace.child name := by
  rcases execution.observe with
    ⟨hierarchy, observed, hierarchyOutputs⟩
  let bodyTrace := ModuleBody.Trace.ofHierarchy hierarchy
  refine ⟨bodyTrace, observed.bodyTrace_wiringHolds, ?_, ?_⟩
  · apply BoundaryTrace.ext
    · rw [Trace.toBoundaryTrace_inputs]
      change (ModuleBody.Trace.ofHierarchy hierarchy).parent.inputs = inputs
      rw [ModuleBody.Trace.ofHierarchy_parent_inputs]
      exact observed.hierarchy_inputs
    · rw [Trace.toBoundaryTrace_outputs]
      change (ModuleBody.Trace.ofHierarchy hierarchy).parent.outputs = outputs
      rw [ModuleBody.Trace.ofHierarchy_parent_outputs]
      exact hierarchyOutputs
  · intro name
    have childExecution :
        (children name).Executes (initialState name)
          (bodyTrace.child name).inputs (bodyTrace.child name).outputs
          (finalState name) := by
      change (children name).Executes (initialState name)
        ((ModuleBody.Trace.ofHierarchy hierarchy).child name).inputs
        ((ModuleBody.Trace.ofHierarchy hierarchy).child name).outputs
        (finalState name)
      rw [ModuleBody.Trace.ofHierarchy_child_inputs,
        ModuleBody.Trace.ofHierarchy_child_outputs]
      exact observed.child name
    refine ⟨childExecution, ?_⟩
    apply BoundaryTrace.ext <;> simp

end ModuleStructure

end Silean
