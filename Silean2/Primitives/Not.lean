import Silean2.ModuleCycleCertified
import Silean2.PrimitivePorts

namespace Silean2.Primitives

open Silean2

@[reducible] def not : Primitive where
  ports := unaryPorts
  localState := emptySignalMap
  outputReads := [.input]
  outputValues := fun inputs _ => fun | .output => !inputs .input
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .input (by simp)]

inductive NotRule | apply
deriving Enumeration
def notOutputRule : CycleOutputRule not.ports emptySignalMap
    (.ofLists [.bit] [.bit]) where
  readsInputs := not.ports.inputs.select .input
  writesOutputs := not.ports.outputs.select .output
  target | (input, ()), _ => (!input, ())
def notCycleContract : ModuleCycleContract not.ports where
  state := emptySignalMap
  RuleName := NotRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, notOutputRule⟩
  stateRule := CycleStateRule.empty not.ports
  outputCoverage := by rfl

@[simp] theorem notOutputRule_holds_iff
    (inputs : not.ports.inputs.Values)
    (state : notCycleContract.state.Values)
    (outputs : not.ports.outputs.Values) :
    notOutputRule.Holds inputs state outputs ↔
      outputs .output = !inputs .input := by
  simp [notOutputRule, CycleOutputRule.Holds, SignalSelection.project,
    SignalSelection.Matches, SignalMap.select]

private def notStateCorresponds (_ : notCycleContract.state.Values)
    (_ : (ModuleStructure.primitive not).State) : Prop := True

private theorem notImplements : Implements (.primitive not) notCycleContract
    notStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change notOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      simp [notOutputRule, CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, not]
  · rfl

def notCertified : ModuleCycleCertified not.ports where
  moduleStructure := .primitive not
  cycleContract := notCycleContract
  certification := {
    stateCorresponds := notStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (not.outputValues inputs state)
      (not.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution not,
    implements := notImplements }
end Silean2.Primitives
