import HTFFT.Silean.InitialReorder.Internal.InitialReorderVerification

/-! Public structural and correctness declarations for the concrete initial
frame reorder. -/

namespace HTFFT.Silean.InitialReorder
open FFT

open _root_.Silean

/-- The concrete reorder hierarchy has exactly one structural solution for
every boundary input and physical state. -/
theorem structuralCertification (depth : Nat)
    (configuration : Configuration depth) :
    ModuleStructuralCertification (moduleStructure depth configuration) :=
  Internal.structuralCertification depth configuration

/-- Every concrete reorder execution satisfies the natural framed global
bit-reversal contract. -/
theorem contract_of_execution (depth : Nat)
    (configuration : Configuration depth)
    {initialState finalState : (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution : (moduleStructure depth configuration).Executes
      initialState inputs outputs finalState) :
    contract configuration execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration execution

end HTFFT.Silean.InitialReorder
