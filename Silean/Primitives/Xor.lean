import Silean.Contracts.Cycle.CycleImplementation
import Silean.Primitives.XorPrimitive

namespace Silean.Primitives

open Silean

inductive XorRule | apply
deriving Enumeration

def xorOutputRule : Contracts.Cycle.CycleOutputRule xor.ports emptySignalMap where
  readsInputs := .all xor.ports.inputs
  writesOutputs := .all xor.ports.outputs
  target inputs _ := fun | .output => xorValue (inputs .left) (inputs .right)

def xorCycleContract : Contracts.Cycle.ModuleCycleContract xor.ports where
  state := emptySignalMap
  RuleName := XorRule
  ruleNames := inferInstance
  outputRule | .apply => xorOutputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty xor.ports
  outputCoverage := by rfl

@[simp] theorem xorOutputRule_holds_iff
    (inputs : xor.ports.inputs.Values)
    (state : xorCycleContract.state.Values)
    (outputs : xor.ports.outputs.Values) :
    xorOutputRule.Holds inputs state outputs ↔
      outputs .output = xorValue (inputs .left) (inputs .right) := by
  simp only [xorOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def stateCorresponds (_ : xorCycleContract.state.Values)
    (_ : (ModuleStructure.primitive xor).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements (.primitive xor) xorCycleContract
    stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change xorOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def xorCertified : Contracts.Cycle.ModuleCycleCertified xor.ports where
  moduleStructure := .primitive xor
  cycleContract := xorCycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
      ⟨ProposedValues.primitive (xor.outputValues inputs state)
        (xor.nextStateValues inputs state), by
          simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
            Primitive.IsSolution, Primitive.OutputsSatisfy,
            Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution xor,
    implements := implements }

end Silean.Primitives
