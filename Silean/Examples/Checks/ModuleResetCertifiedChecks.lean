import Silean.ModuleResetCertified

namespace Silean.Examples.Checks.ModuleResetCertified

open Silean

section AbstractStructure

variable {ports : ModulePorts}
variable (moduleStructure : ModuleStructure ports)
variable (contract : ModuleResetContract ports)
variable (available : moduleStructure.HasSolution)
variable (refines : ImplementsResetContract moduleStructure contract)

def certified : Silean.ModuleResetCertified ports where
  moduleStructure := moduleStructure
  resetContract := contract
  hasSolution := available
  implements := refines

example (initialState : moduleStructure.State)
    (inputs : List ports.inputs.Values) :
    ∃ outputs finalState,
      moduleStructure.Executes initialState inputs outputs finalState :=
  (certified moduleStructure contract available refines).execution_exists
    initialState inputs

example (initialState : moduleStructure.State)
    (inputs : List ports.inputs.Values) :
    ∃ outputs finalState,
      moduleStructure.Executes initialState inputs outputs finalState ∧
        contract.Accepts inputs outputs :=
  (certified moduleStructure contract available refines).accepted_execution_exists
    initialState inputs

example {initialState finalState : moduleStructure.State}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (execution : moduleStructure.Executes initialState inputs outputs finalState) :
    contract.Accepts inputs outputs :=
  (certified moduleStructure contract available refines).accepts_execution execution

/-! The prefix may itself contain an earlier reset. Certification of the
later reset-starting suffix depends on neither that history nor the structural
state reached by it. -/
example {initialState finalState : moduleStructure.State}
    {prefixInputs : List ports.inputs.Values}
    {laterReset : ports.inputs.Values} {suffixInputs : List ports.inputs.Values}
    {prefixOutputs : List ports.outputs.Values}
    {resetOutput : ports.outputs.Values} {suffixOutputs : List ports.outputs.Values}
    (prefixLengths : prefixOutputs.length = prefixInputs.length)
    (asserted : contract.resetAsserted laterReset = true)
    (execution : moduleStructure.Executes initialState
      (prefixInputs ++ laterReset :: suffixInputs)
      (prefixOutputs ++ resetOutput :: suffixOutputs) finalState) :
    ∃ finalSynchronization,
      contract.TraceMatches (some contract.resetState)
        suffixInputs suffixOutputs finalSynchronization :=
  (certified moduleStructure contract available refines).matches_after_reset
    prefixLengths asserted execution

end AbstractStructure

end Silean.Examples.Checks.ModuleResetCertified
