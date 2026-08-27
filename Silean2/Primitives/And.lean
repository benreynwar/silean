import Silean2.ModuleCycleCertified
import Silean2.PrimitivePorts

namespace Silean2.Primitives

open Silean2

@[reducible] def and : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun | .output => inputs .left && inputs .right
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

inductive AndRule | apply
deriving Enumeration
def andOutputRule : CycleOutputRule and.ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (and.ports.inputs.select .right).prepend .left
  writesOutputs := and.ports.outputs.select .output
  target | (left, (right, ())), _ => (left && right, ())
def andCycleContract : ModuleCycleContract and.ports where
  state := emptySignalMap
  RuleName := AndRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, andOutputRule⟩
  stateRule := CycleStateRule.empty and.ports
  outputCoverage := by rfl

@[simp] theorem andOutputRule_holds_iff
    (inputs : and.ports.inputs.Values)
    (state : andCycleContract.state.Values)
    (outputs : and.ports.outputs.Values) :
    andOutputRule.Holds inputs state outputs ↔
      outputs .output = (inputs .left && inputs .right) := by
  simp [andOutputRule, CycleOutputRule.Holds, SignalSelection.project,
    SignalSelection.Matches, SignalMap.select, SignalSelection.prepend]

private def andStateCorresponds (_ : andCycleContract.state.Values)
    (_ : (ModuleStructure.primitive and).State) : Prop := True

private theorem andImplements : Implements (.primitive and) andCycleContract
    andStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change andOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      simp [andOutputRule, CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, SignalSelection.prepend, and]
  · rfl

def andCertified : ModuleCycleCertified and.ports where
  moduleStructure := .primitive and
  cycleContract := andCycleContract
  certification := {
    stateCorresponds := andStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (and.outputValues inputs state)
      (and.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution and,
    implements := andImplements }
end Silean2.Primitives
