import Silean2.ModuleResetContract
import Silean2.StructuralExecution

namespace Silean2

universe u

/-! Reset certification relates two independently meaningful descriptions. It
stores only the trace-refinement fact, not the witnesses used to prove it. -/

def ImplementsResetContract (moduleStructure : ModuleStructure ports)
    (resetContract : ModuleResetContract ports) : Prop :=
  ∀ initialState inputs outputs finalState,
    moduleStructure.Executes initialState inputs outputs finalState →
      resetContract.Accepts inputs outputs

structure ModuleResetCertified (ports : ModulePorts) where
  moduleStructure : ModuleStructure ports
  resetContract : ModuleResetContract.{u} ports
  implements : ImplementsResetContract moduleStructure resetContract

namespace ModuleResetCertified

theorem accepts_execution (certified : ModuleResetCertified ports)
    {initialState finalState : certified.moduleStructure.State}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (execution : certified.moduleStructure.Executes initialState inputs outputs
      finalState) :
    certified.resetContract.Accepts inputs outputs :=
  certified.implements initialState inputs outputs finalState execution

/-! After an initial reset cycle, the existential synchronization state is
known exactly and the remainder is checked cycle-for-cycle. -/
theorem matches_after_initial_reset (certified : ModuleResetCertified ports)
    {initialState finalState : certified.moduleStructure.State}
    {resetInput : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {resetOutput : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (asserted : certified.resetContract.resetAsserted resetInput = true)
    (execution : certified.moduleStructure.Executes initialState
      (resetInput :: inputs) (resetOutput :: outputs) finalState) :
    ∃ finalSynchronization,
      certified.resetContract.TraceMatches
        (some certified.resetContract.resetState)
        inputs outputs finalSynchronization := by
  rcases certified.accepts_execution execution with
    ⟨finalSynchronization, trace⟩
  exact ⟨finalSynchronization,
    (ModuleResetContract.TraceMatches.cons_reset_iff asserted).mp trace⟩

/-! The same statement applies after any prefix. Splitting the structural
execution exposes the reset-starting suffix; the prefix's state is irrelevant. -/
theorem matches_after_reset (certified : ModuleResetCertified ports)
    {initialState finalState : certified.moduleStructure.State}
    {prefixInputs : List ports.inputs.Values}
    {resetInput : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {prefixOutputs : List ports.outputs.Values}
    {resetOutput : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (prefixLengths : prefixOutputs.length = prefixInputs.length)
    (asserted : certified.resetContract.resetAsserted resetInput = true)
    (execution : certified.moduleStructure.Executes initialState
      (prefixInputs ++ resetInput :: inputs)
      (prefixOutputs ++ resetOutput :: outputs) finalState) :
    ∃ finalSynchronization,
      certified.resetContract.TraceMatches
        (some certified.resetContract.resetState)
        inputs outputs finalSynchronization := by
  rcases ModuleStructure.Executes.split execution prefixLengths with
    ⟨middleState, _, suffix⟩
  exact certified.matches_after_initial_reset asserted suffix

end ModuleResetCertified

end Silean2
