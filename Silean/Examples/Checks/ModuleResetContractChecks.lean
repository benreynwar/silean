import Silean.Contracts.Reset.ResetContract
import Silean.Foundation.DeriveEnumeration

namespace Silean.Examples.Checks.ResetContract

open Silean

inductive Input
  | reset
  | push
deriving Enumeration

inductive Output
  | valid
  | payload
deriving Enumeration

def ports : ModulePorts where
  inputs := EnumeratedMap.of Input fun _ => .bit
  outputs := EnumeratedMap.of Output fun _ => .bit

def input (reset push : Bool) : ports.inputs.Values
  | .reset => reset
  | .push => push

def output (valid payload : Bool) : ports.outputs.Values
  | .valid => valid
  | .payload => payload

def pushAsserted (inputs : ports.inputs.Values) : Bool :=
  cast (congrArg SignalType.Denote
    (show ports.inputs.signalType Input.push = .bit by rfl))
    (inputs .push)

@[simp] theorem pushAsserted_input (reset push : Bool) :
    pushAsserted (input reset push) = push := by
  rfl

def contract : Silean.Contracts.Reset.ModuleResetContract ports where
  State := List Bool
  resetInput := .reset
  resetInputType := rfl
  resetState := []
  step inputs state :=
    (fun
      | .valid => .exact (!state.isEmpty)
      | .payload => match state with
        | [] => .dontCare
        | head :: _ => .exact head,
      if pushAsserted inputs then state ++ [true] else state)

example : contract.resetAsserted (input true false) = true := rfl

example : ports.outputs.Matches
    (contract.step (input false false) []).1 (output false true) := by
  intro name
  cases name <;> change BitExpectation.Matches _ _ <;>
    simp [contract, output, BitExpectation.exact, BitExpectation.Matches]

example : ¬ports.outputs.Matches
    (contract.step (input false false) [true]).1 (output false true) := by
  intro outputMatches
  have valid := outputMatches Output.valid
  change BitExpectation.Matches _ _ at valid
  simp [contract, output, BitExpectation.exact, BitExpectation.Matches] at valid

example : contract.TraceMatches none
    [input false false, input true false, input false true, input false false,
      input true false, input false false]
    [output true false, output true true, output false false, output true true,
      output false false, output false true]
    (some []) := by
  refine Execution.Trace.cons _ _ (.beforeReset rfl) ?_
  refine Execution.Trace.cons _ _ (.reset rfl) ?_
  refine Execution.Trace.cons _ _ (.ordinary rfl ?_) ?_
  · intro name
    cases name <;> change BitExpectation.Matches _ _ <;>
      simp [contract, output, BitExpectation.exact,
        BitExpectation.Matches]
  refine Execution.Trace.cons _ _ (.ordinary rfl ?_) ?_
  · intro name
    cases name <;> change BitExpectation.Matches _ _ <;>
      simp [contract, output, BitExpectation.exact,
        BitExpectation.Matches]
  refine Execution.Trace.cons _ _ (.reset rfl) ?_
  refine Execution.Trace.cons _ _ (.ordinary rfl ?_) ?_
  · intro name
    cases name <;> change BitExpectation.Matches _ _ <;>
      simp [contract, output, BitExpectation.exact,
        BitExpectation.Matches]
  exact .nil (some [])

example (inputs : List ports.inputs.Values) (outputs : List ports.outputs.Values)
    (lengths : outputs.length = inputs.length)
    (ordinary : ∀ input, input ∈ inputs → contract.resetAsserted input = false) :
    contract.TraceMatches none inputs outputs none :=
  Silean.Contracts.Reset.ModuleResetContract.TraceMatches.before_first_reset contract
    lengths ordinary

end Silean.Examples.Checks.ResetContract
