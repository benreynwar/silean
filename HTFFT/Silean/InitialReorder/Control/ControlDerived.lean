import HTFFT.Silean.InitialReorder.Control.Internal.ControlVerification

/-! Public placement and correctness interface for initial-reorder control. -/

namespace HTFFT.Silean.InitialReorder.Control

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

noncomputable def place (addressWidth : Nat) (i_first : Net .bit) :
    Builder (ports.OutputNets addressWidth) :=
  ports.placeIndexed addressWidth "initial_reorder_control"
    (moduleStructure addressWidth) (naming addressWidth) i_first

attribute [circuit_description] place

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

end HTFFT.Silean.InitialReorder.Control
