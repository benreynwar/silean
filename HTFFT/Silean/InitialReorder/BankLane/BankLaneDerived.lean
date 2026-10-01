import HTFFT.Silean.InitialReorder.BankLane.Internal.BankLaneVerification

namespace HTFFT.Silean.InitialReorder.BankLane
open FFT

open _root_.Silean

theorem contract_of_execution (depth : Nat)
    (configuration : Configuration depth)
    {initialState finalState : (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution : (moduleStructure depth configuration).Executes
      initialState inputs outputs finalState) :
    contract configuration execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration execution

end HTFFT.Silean.InitialReorder.BankLane
