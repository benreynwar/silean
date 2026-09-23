import Silean.Semantics.StructuralObservation
import SileanTests.Fixtures.DoubleNot

namespace SileanTests.ModuleBodyTraceChecks

open Silean

/-! These are deliberately ordinary predicates on boundary traces.  The
example does not depend on `ModuleCycleContract` or any other particular
contract language. -/

def NotTrace (trace : BoundaryTrace Primitives.not.ports) : Prop :=
  ∀ step ∈ trace, step.outputs .output = !step.inputs .input

def IdentityTrace (trace : BoundaryTrace Fixtures.DoubleNot.ports) : Prop :=
  ∀ step ∈ trace, step.outputs .result = step.inputs .value

/-- The permanent body wiring composes arbitrary predicates supplied for its
two immediate children. -/
theorem identityTrace_of_children
    (trace : Fixtures.DoubleNot.body.Trace)
    (wiring : trace.WiringHolds)
    (firstCorrect : NotTrace (trace.child .first))
    (secondCorrect : NotTrace (trace.child .second)) :
    IdentityTrace trace.parent := by
  intro parentStep parentMember
  rcases List.mem_map.mp parentMember with
    ⟨bodyStep, bodyMember, rfl⟩
  have stepWiring := wiring.step bodyMember
  have firstStep := firstCorrect (bodyStep.child .first)
    (trace.mem_child_of_mem .first bodyMember)
  have secondStep := secondCorrect (bodyStep.child .second)
    (trace.mem_child_of_mem .second bodyMember)
  have firstInput := stepWiring.child_input .first .input
  change (bodyStep.child .first).inputs .input =
    (Fixtures.DoubleNot.context.moduleInput .value).value
      bodyStep.parent.inputs (fun child => (bodyStep.child child).outputs)
        at firstInput
  rw [EndpointContext.moduleInput_value] at firstInput
  have secondInput := stepWiring.child_input .second .input
  change (bodyStep.child .second).inputs .input =
    (Fixtures.DoubleNot.context.instanceOutput .first .output).value
      bodyStep.parent.inputs (fun child => (bodyStep.child child).outputs)
        at secondInput
  rw [EndpointContext.instanceOutput_value] at secondInput
  have parentOutput := stepWiring.parent_output .result
  change bodyStep.parent.outputs .result =
    (Fixtures.DoubleNot.context.instanceOutput .second .output).value
      bodyStep.parent.inputs (fun child => (bodyStep.child child).outputs)
        at parentOutput
  rw [EndpointContext.instanceOutput_value] at parentOutput
  simp_all

/-- A concrete execution of the primitive inverter discharges the custom
child trace predicate without passing through a cycle-contract API. -/
theorem notTrace_of_execution
    {initialState finalState :
      (ModuleStructure.primitive Primitives.not).State}
    {inputs : List Primitives.not.ports.inputs.Values}
    {outputs : List Primitives.not.ports.outputs.Values}
    (execution : (ModuleStructure.primitive Primitives.not).Executes
      initialState inputs outputs finalState) :
    NotTrace execution.toBoundaryTrace := by
  induction execution with
  | nil =>
      simp [NotTrace]
  | @cons currentState nextState finalState remainingInputs remainingOutputs
      input output transition rest induction =>
      rw [Trace.toBoundaryTrace_cons input output transition rest]
      intro step member
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · rcases transition.solution_exists with
          ⟨hierStep, solution, boundaryEqual⟩
        have inputsEqual : hierStep.inputs = input :=
          congrArg CycleStep.inputs boundaryEqual
        have outputsEqual : hierStep.outputs = output :=
          congrArg CycleStep.outputs boundaryEqual
        calc
          output .output = hierStep.outputs .output :=
            congrFun outputsEqual.symm .output
          _ = !hierStep.inputs .input := by
            simpa [Primitive.IsSolution, Primitive.OutputsSatisfy,
              Primitives.not] using congrFun solution.1 .output
          _ = !input .input :=
            congrArg (fun value => !value) (congrFun inputsEqual .input)
      · exact induction step later

/-- Complete handoff: a concrete execution supplies the implementation-
independent body trace, concrete children discharge the assumed predicates,
and the top-down body theorem returns a fact about the original parent
boundary trace. -/
theorem concrete_doubleNot_identity
    {initialState finalState : Fixtures.DoubleNot.moduleStructure.State}
    {inputs : List Fixtures.DoubleNot.ports.inputs.Values}
    {outputs : List Fixtures.DoubleNot.ports.outputs.Values}
    (execution : Fixtures.DoubleNot.moduleStructure.Executes
      initialState inputs outputs finalState) :
    IdentityTrace execution.toBoundaryTrace := by
  unfold Fixtures.DoubleNot.moduleStructure at execution ⊢
  rcases execution.toBodyTrace with
    ⟨bodyTrace, wiring, parentEqual, childExecutions⟩
  have firstCorrect : NotTrace (bodyTrace.child .first) := by
    rcases childExecutions .first with
      ⟨childExecution, childTraceEqual⟩
    rw [← childTraceEqual]
    exact notTrace_of_execution childExecution
  have secondCorrect : NotTrace (bodyTrace.child .second) := by
    rcases childExecutions .second with
      ⟨childExecution, childTraceEqual⟩
    rw [← childTraceEqual]
    exact notTrace_of_execution childExecution
  have parentCorrect :=
    identityTrace_of_children bodyTrace wiring firstCorrect secondCorrect
  rw [parentEqual] at parentCorrect
  exact parentCorrect

end SileanTests.ModuleBodyTraceChecks
