import HTFFT.Silean.InitialReorder.BankLane.Internal.BankLaneStep
import Silean.Contracts.Cycle.CycleTrace
import Silean.Semantics.StructuralObservation

namespace HTFFT.Silean.InitialReorder.BankLane.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev BankState (configuration : Configuration depth) :=
  (RegisterBank.cycleContract (sampleType configuration)
    (InitialReorder.addressWidth configuration) 1).state.Values

private abbrev OutputState (configuration : Configuration depth) :=
  (Register.cycleContract (sampleType configuration)).state.Values

private theorem laneTrace (depth : Nat)
    (configuration : Configuration depth)
    (hierarchy : List (HierStep (moduleStructure depth configuration)))
    (solutions : ∀ step ∈ hierarchy,
      (moduleStructure depth configuration).IsSolution step)
    {bankInitial bankFinal : BankState configuration}
    {outputInitial outputFinal : OutputState configuration}
    (bankTrace : Trace
      (RegisterBank.cycleContract (sampleType configuration)
        (InitialReorder.addressWidth configuration) 1).Transition bankInitial
      (hierarchy.map fun step => (step.children .bank).inputs)
      (hierarchy.map fun step => (step.children .bank).outputs) bankFinal)
    (outputTrace : Trace
      (Register.cycleContract (sampleType configuration)).Transition outputInitial
      (hierarchy.map fun step => (step.children .outputRegister).inputs)
      (hierarchy.map fun step => (step.children .outputRegister).outputs)
      outputFinal) :
    Trace (Transition configuration)
      (logicalState configuration bankInitial outputInitial)
      (hierarchy.map HierStep.inputs) (hierarchy.map HierStep.outputs)
      (logicalState configuration bankFinal outputFinal) := by
  induction hierarchy generalizing bankInitial outputInitial with
  | nil =>
      cases bankTrace
      cases outputTrace
      exact .nil _
  | cons step hierarchy induction =>
      cases bankTrace with
      | cons _ _ bankAllowed bankRest =>
        cases outputTrace with
        | cons _ _ outputAllowed outputRest =>
          refine .cons step.inputs step.outputs
            (transition_of_solution depth configuration
              (solutions step (by simp)) bankAllowed outputAllowed) ?_
          apply induction
          · intro later member
            exact solutions later (by simp [member])
          · exact bankRest
          · exact outputRest

theorem contract_of_execution (depth : Nat)
    (configuration : Configuration depth)
    {initialState finalState : (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution : (moduleStructure depth configuration).Executes
      initialState inputs outputs finalState) :
    contract configuration execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let bankExecution := observed.child .bank
  let outputExecution := observed.child .outputRegister
  simp only [structuralChildren] at bankExecution outputExecution
  obtain ⟨bankInitial, bankFinal, bankTrace⟩ :=
    (RegisterBank.certification (sampleType configuration)
      (InitialReorder.addressWidth configuration) 1).accepts_of_executes
      bankExecution
  obtain ⟨outputInitial, outputFinal, outputTrace⟩ :=
    (Register.certification (sampleType configuration)).accepts_of_executes
      outputExecution
  have parentTrace := laneTrace depth configuration hierarchy
    (fun step member => observed.solution_of_mem step member)
    bankTrace outputTrace
  unfold contract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  refine ⟨logicalState configuration bankInitial outputInitial,
    logicalState configuration bankFinal outputFinal, ?_⟩
  rw [← observed.hierarchy_inputs, ← rootOutputs]
  exact parentTrace

end HTFFT.Silean.InitialReorder.BankLane.Internal
