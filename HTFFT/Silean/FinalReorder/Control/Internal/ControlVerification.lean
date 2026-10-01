import HTFFT.Silean.FinalReorder.Control.Internal.ControlStep
import Silean.Contracts.Cycle.CycleTrace
import Silean.Semantics.StructuralObservation

/-! Trace refinement for concrete final-reorder control. -/

namespace HTFFT.Silean.FinalReorder.Control.Internal

open _root_.Silean
open _root_.Silean.Modules

private abbrev CounterState (addressWidth : Nat) :=
  (EnabledResetCounter.cycleContract addressWidth
    (oneAddress addressWidth)).state.Values

private theorem controlTrace (addressWidth : Nat)
    (hierarchy : List (HierStep (moduleStructure addressWidth)))
    (solutions : ∀ step ∈ hierarchy,
      (moduleStructure addressWidth).IsSolution step)
    {writeInitial writeFinal readInitial readFinal : CounterState addressWidth}
    (writeTrace : Trace
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Transition writeInitial
      (hierarchy.map fun step => (step.children .writeCounter).inputs)
      (hierarchy.map fun step => (step.children .writeCounter).outputs)
      writeFinal)
    (readTrace : Trace
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Transition readInitial
      (hierarchy.map fun step => (step.children .readCounter).inputs)
      (hierarchy.map fun step => (step.children .readCounter).outputs)
      readFinal) :
    Trace (Transition addressWidth)
      (controlState addressWidth writeInitial readInitial)
      (hierarchy.map HierStep.inputs) (hierarchy.map HierStep.outputs)
      (controlState addressWidth writeFinal readFinal) := by
  induction hierarchy generalizing writeInitial readInitial with
  | nil =>
      cases writeTrace
      cases readTrace
      exact .nil _
  | cons step hierarchy induction =>
      cases writeTrace with
      | cons _ _ writeAllowed writeRest =>
        cases readTrace with
        | cons _ _ readAllowed readRest =>
          refine .cons step.inputs step.outputs
            (transition_of_solution addressWidth
              (solutions step (by simp)) writeAllowed readAllowed) ?_
          apply induction
          · intro later member
            exact solutions later (by simp [member])
          · exact writeRest
          · exact readRest

/-- Every concrete controller execution satisfies its natural hidden-state
trace contract. -/
theorem contract_of_execution (addressWidth : Nat)
    {initialState finalState : (moduleStructure addressWidth).State}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (execution : (moduleStructure addressWidth).Executes
      initialState inputs outputs finalState) :
    contract addressWidth execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let writeExecution := observed.child .writeCounter
  let readExecution := observed.child .readCounter
  simp only [structuralChildren] at writeExecution readExecution

  obtain ⟨writeInitial, writeFinal, writeTrace⟩ :=
    (EnabledResetCounter.certification addressWidth
      (oneAddress addressWidth)).accepts_of_executes writeExecution
  obtain ⟨readInitial, readFinal, readTrace⟩ :=
    (EnabledResetCounter.certification addressWidth
      (oneAddress addressWidth)).accepts_of_executes readExecution

  have parentTrace := controlTrace addressWidth hierarchy
    (fun step member => observed.solution_of_mem step member)
    writeTrace readTrace
  unfold contract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  refine ⟨controlState addressWidth writeInitial readInitial,
    controlState addressWidth writeFinal readFinal, ?_⟩
  rw [← observed.hierarchy_inputs, ← rootOutputs]
  exact parentTrace

end HTFFT.Silean.FinalReorder.Control.Internal
