import Silean.Semantics.StructuralExecution

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

end ModuleStructure

end Silean
