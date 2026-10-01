import HTFFT.Silean.FinalReorder.Control.Internal.ControlVerification

/-! Public structural interface for final-reorder control. -/

namespace HTFFT.Silean.FinalReorder.Control

open _root_.Silean

theorem structuralCertification (addressWidth : Nat) :
    ModuleStructuralCertification (moduleStructure addressWidth) :=
  Internal.structuralCertification addressWidth

theorem contract_of_execution (addressWidth : Nat)
    {initialState finalState : (moduleStructure addressWidth).State}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (execution : (moduleStructure addressWidth).Executes
      initialState inputs outputs finalState) :
    contract addressWidth execution.toBoundaryTrace :=
  Internal.contract_of_execution addressWidth execution

end HTFFT.Silean.FinalReorder.Control
