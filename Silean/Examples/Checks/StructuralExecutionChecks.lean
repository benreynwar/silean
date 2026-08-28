import Silean.Semantics.StructuralExecution
import Silean.Primitives.NotPrimitive
import Silean.Primitives.RegisterPrimitive

namespace Silean.Examples.Checks.StructuralExecution

open Silean

def notModule : ModuleStructure Primitives.not.ports :=
  .primitive Primitives.not

def notInputs (value : Bool) : Primitives.not.ports.inputs.Values
  | .input => value

def notOutputs (value : Bool) : Primitives.not.ports.outputs.Values
  | .output => value

def emptyState : notModule.State := SignalMap.emptyValues

example : notModule.Transition (notInputs false) emptyState
    (notOutputs true) emptyState := by
  refine ModuleStructure.transition_of_solution (proposal := ProposedValues.primitive
    (notOutputs true) emptyState) ?_
  change Primitives.not.IsSolution (notInputs false) emptyState emptyState
    (notOutputs true)
  exact ⟨rfl, rfl⟩

example : notModule.Executes emptyState [notInputs false, notInputs true]
    [notOutputs true, notOutputs false] emptyState := by
  apply Execution.Trace.cons (notInputs false) (notOutputs true)
  · refine ModuleStructure.transition_of_solution (proposal := ProposedValues.primitive
      (notOutputs true) emptyState) ?_
    change Primitives.not.IsSolution (notInputs false) emptyState emptyState
      (notOutputs true)
    exact ⟨rfl, rfl⟩
  · change notModule.Executes emptyState [notInputs true]
      [notOutputs false] emptyState
    rw [ModuleStructure.Executes.single_iff]
    refine ModuleStructure.transition_of_solution (proposal := ProposedValues.primitive
      (notOutputs false) emptyState) ?_
    change Primitives.not.IsSolution (notInputs true) emptyState emptyState
      (notOutputs false)
    exact ⟨rfl, rfl⟩

def registerModule : ModuleStructure Primitives.register.ports :=
  .primitive Primitives.register

def registerInputs (value : Bool) : Primitives.register.ports.inputs.Values
  | .input => value

def registerState (value : Bool) : registerModule.State
  | .stored => value

def registerOutputs (value : Bool) : Primitives.register.ports.outputs.Values
  | .output => value

def registerProposal (current input : Bool) : ProposedValues registerModule :=
  ProposedValues.primitive (registerOutputs current) (registerState input)

theorem registerSolution (current input : Bool) :
    registerModule.IsSolution (registerInputs input) (registerState current)
      (registerProposal current input) := by
  change Primitives.register.IsSolution (registerInputs input)
    (registerState current) (registerState input) (registerOutputs current)
  exact ⟨rfl, rfl⟩

theorem registerHasSolution : registerModule.HasSolution := by
  intro inputs state
  refine ⟨ProposedValues.primitive
    (Primitives.register.outputValues inputs state)
    (Primitives.register.nextStateValues inputs state), ?_⟩
  change Primitives.register.IsSolution inputs state
    (Primitives.register.nextStateValues inputs state)
    (Primitives.register.outputValues inputs state)
  exact ⟨rfl, rfl⟩

example : registerModule.Executes (registerState false)
    [registerInputs true, registerInputs false]
    [registerOutputs false, registerOutputs true] (registerState false) := by
  apply Execution.Trace.cons (registerInputs true) (registerOutputs false)
  · exact ModuleStructure.transition_of_solution (registerSolution false true)
  · change registerModule.Executes (registerState true) [registerInputs false]
      [registerOutputs true] (registerState false)
    rw [ModuleStructure.Executes.single_iff]
    exact ModuleStructure.transition_of_solution (registerSolution true false)

example : ∃ outputs finalState,
    registerModule.Executes (registerState false)
      [registerInputs true, registerInputs false] outputs finalState :=
  registerHasSolution.execution_exists _ _

example : registerModule.HasExactlyOneSolution :=
  ⟨registerHasSolution, Primitives.register.hasAtMostOneSolution⟩

end Silean.Examples.Checks.StructuralExecution
