import Silean2.ModuleCycleCertified
import Silean2.PrimitivePorts

namespace Silean2.Primitives

open Silean2

@[reducible] def eq : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun
    | .output => (inputs .left && inputs .right) ||
        (!inputs .left && !inputs .right)
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

inductive EqRule | apply
deriving Enumeration
def eqOutputRule : CycleOutputRule eq.ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (eq.ports.inputs.select .right).prepend .left
  writesOutputs := eq.ports.outputs.select .output
  target
    | (left, (right, ())), _ =>
        ((left && right) || (!left && !right), ())
def eqCycleContract : ModuleCycleContract eq.ports where
  state := emptySignalMap
  RuleName := EqRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, eqOutputRule⟩
  stateRule := CycleStateRule.empty eq.ports
  outputCoverage := by rfl

private def eqStateCorresponds (_ : eqCycleContract.state.Values)
    (_ : (ModuleStructure.primitive eq).State) : Prop := True

private theorem eqImplements : Implements (.primitive eq) eqCycleContract
    eqStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change eqOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      simp [eqOutputRule, CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, SignalSelection.prepend, eq]
  · rfl

def eqCertified : ModuleCycleCertified eq.ports where
  moduleStructure := .primitive eq
  cycleContract := eqCycleContract
  stateCorresponds := eqStateCorresponds
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (eq.outputValues inputs state)
      (eq.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩
  structuralResultUnique := Primitive.hasAtMostOneSolution eq
  implements := eqImplements
end Silean2.Primitives
