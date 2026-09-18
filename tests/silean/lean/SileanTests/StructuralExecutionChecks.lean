import Silean.Semantics.StructuralExecution
import Silean.Primitives.NotPrimitive
import Silean.Primitives.RegisterPrimitive

namespace SileanTests.StructuralExecution

open Silean

def notModule : ModuleStructure Primitives.not.ports :=
  .primitive Primitives.not

def notInputs (value : Bool) : Primitives.not.ports.inputs.Values
  | .input => value

def notOutputs (value : Bool) : Primitives.not.ports.outputs.Values
  | .output => value

def emptyState : notModule.State := SignalMap.emptyValues

def notHierStep (input output : Bool) : HierStep notModule :=
  { inputs := notInputs input
    currentState := emptyState
    outputs := notOutputs output
    nextState := emptyState }

example : notModule.Transition (notInputs false) emptyState
    (notOutputs true) emptyState := by
  refine ModuleStructure.transition_of_solution
    (hierStep := notHierStep false true) ?_
  change Primitives.not.IsSolution (notInputs false) emptyState emptyState
    (notOutputs true)
  exact ⟨rfl, rfl⟩

example : notModule.Executes emptyState [notInputs false, notInputs true]
    [notOutputs true, notOutputs false] emptyState := by
  apply Trace.cons (notInputs false) (notOutputs true)
  · refine ModuleStructure.transition_of_solution
      (hierStep := notHierStep false true) ?_
    change Primitives.not.IsSolution (notInputs false) emptyState emptyState
      (notOutputs true)
    exact ⟨rfl, rfl⟩
  · change notModule.Executes emptyState [notInputs true]
      [notOutputs false] emptyState
    rw [ModuleStructure.Executes.single_iff]
    refine ModuleStructure.transition_of_solution
      (hierStep := notHierStep true false) ?_
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

def registerHierStep (current input : Bool) : HierStep registerModule :=
  { inputs := registerInputs input
    currentState := registerState current
    outputs := registerOutputs current
    nextState := registerState input }

theorem registerSolution (current input : Bool) :
    registerModule.IsSolution (registerHierStep current input) := by
  change Primitives.register.IsSolution (registerInputs input)
    (registerState current) (registerState input) (registerOutputs current)
  exact ⟨rfl, rfl⟩

theorem registerHasSolution : registerModule.HasSolution := by
  exact Primitives.register.hasSolution

example : registerModule.Executes (registerState false)
    [registerInputs true, registerInputs false]
    [registerOutputs false, registerOutputs true] (registerState false) := by
  apply Trace.cons (registerInputs true) (registerOutputs false)
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

end SileanTests.StructuralExecution
