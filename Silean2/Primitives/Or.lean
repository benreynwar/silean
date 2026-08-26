import Silean2.ModuleCycleCertified
import Silean2.PrimitivePorts

namespace Silean2.Primitives

open Silean2

@[reducible] def or : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun | .output => inputs .left || inputs .right
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

inductive OrRule | apply
deriving Enumeration
def orOutputRule : CycleOutputRule or.ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (or.ports.inputs.select .right).prepend .left
  writesOutputs := or.ports.outputs.select .output
  target | (left, (right, ())), _ => (left || right, ())
def orCycleContract : ModuleCycleContract or.ports where
  state := emptySignalMap
  RuleName := OrRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, orOutputRule⟩
  stateRule := CycleStateRule.empty or.ports
  outputCoverage := by rfl

private def orStateCorresponds (_ : orCycleContract.state.Values)
    (_ : (ModuleStructure.primitive or).State) : Prop := True

private theorem orImplements : Implements (.primitive or) orCycleContract
    orStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change orOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      simp [orOutputRule, CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, SignalSelection.prepend, or]
  · rfl

def orCertified : ModuleCycleCertified or.ports where
  moduleStructure := .primitive or
  cycleContract := orCycleContract
  stateCorresponds := orStateCorresponds
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (or.outputValues inputs state)
      (or.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩
  structuralResultUnique := Primitive.hasAtMostOneSolution or
  implements := orImplements
end Silean2.Primitives
