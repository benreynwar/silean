import HTFFT.Silean.InitialReorder.Control.Internal.ControlStep
import Silean.Contracts.Cycle.CycleTrace
import Silean.Semantics.StructuralObservation

/-! Trace refinement for concrete initial-reorder control. -/

namespace HTFFT.Silean.InitialReorder.Control.Internal

open _root_.Silean
open _root_.Silean.Modules

private abbrev AddressCounterState (addressWidth : Nat) :=
  (EnabledResetCounter.cycleContract addressWidth
    (oneAddress addressWidth)).state.Values

private abbrev OrientationCounterState :=
  (EnabledResetCounter.cycleContract 1
    (orientationValue false)).state.Values

private theorem controlTrace (addressWidth : Nat)
    (hierarchy : List (HierStep (moduleStructure addressWidth)))
    (solutions : ∀ step ∈ hierarchy,
      (moduleStructure addressWidth).IsSolution step)
    {addressInitial addressFinal : AddressCounterState addressWidth}
    {orientationInitial orientationFinal : OrientationCounterState}
    (addressTrace : Trace
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Transition addressInitial
      (hierarchy.map fun step => (step.children .addressCounter).inputs)
      (hierarchy.map fun step => (step.children .addressCounter).outputs)
      addressFinal)
    (orientationTrace : Trace
      (EnabledResetCounter.cycleContract 1
        (orientationValue false)).Transition orientationInitial
      (hierarchy.map fun step => (step.children .orientationCounter).inputs)
      (hierarchy.map fun step => (step.children .orientationCounter).outputs)
      orientationFinal) :
    Trace (Transition addressWidth)
      (controlState addressWidth addressInitial orientationInitial)
      (hierarchy.map HierStep.inputs) (hierarchy.map HierStep.outputs)
      (controlState addressWidth addressFinal orientationFinal) := by
  induction hierarchy generalizing addressInitial orientationInitial with
  | nil =>
      cases addressTrace
      cases orientationTrace
      exact .nil _
  | cons step hierarchy induction =>
      cases addressTrace with
      | cons _ _ addressAllowed addressRest =>
        cases orientationTrace with
        | cons _ _ orientationAllowed orientationRest =>
          refine .cons step.inputs step.outputs
            (transition_of_solution addressWidth
              (solutions step (by simp)) addressAllowed orientationAllowed) ?_
          apply induction
          · intro later member
            exact solutions later (by simp [member])
          · exact addressRest
          · exact orientationRest

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
  let addressExecution := observed.child .addressCounter
  let orientationExecution := observed.child .orientationCounter
  simp only [structuralChildren] at addressExecution orientationExecution

  obtain ⟨addressInitial, addressFinal, addressTrace⟩ :=
    (EnabledResetCounter.certification addressWidth
      (oneAddress addressWidth)).accepts_of_executes addressExecution
  obtain ⟨orientationInitial, orientationFinal, orientationTrace⟩ :=
    (EnabledResetCounter.certification 1
      (orientationValue false)).accepts_of_executes orientationExecution

  have parentTrace := controlTrace addressWidth hierarchy
    (fun step member => observed.solution_of_mem step member)
    addressTrace orientationTrace
  unfold contract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  refine ⟨controlState addressWidth addressInitial orientationInitial,
    controlState addressWidth addressFinal orientationFinal, ?_⟩
  rw [← observed.hierarchy_inputs, ← rootOutputs]
  exact parentTrace

end HTFFT.Silean.InitialReorder.Control.Internal
