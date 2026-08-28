import Silean.Contracts.Cycle.CycleImplementation
import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

/-- Stateless one-bit equality primitive. -/
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
def eqOutputRule : Contracts.Cycle.CycleOutputRule eq.ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (eq.ports.inputs.select .right).prepend .left
  writesOutputs := eq.ports.outputs.select .output
  target
    | (left, (right, ())), _ =>
        ((left && right) || (!left && !right), ())
def eqCycleContract : Contracts.Cycle.ModuleCycleContract eq.ports where
  state := emptySignalMap
  RuleName := EqRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, eqOutputRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty eq.ports
  outputCoverage := by rfl

@[simp] theorem eqOutputRule_holds_iff
    (inputs : eq.ports.inputs.Values)
    (state : eqCycleContract.state.Values)
    (outputs : eq.ports.outputs.Values) :
    eqOutputRule.Holds inputs state outputs ↔
      outputs .output =
        ((inputs .left && inputs .right) ||
          (!inputs .left && !inputs .right)) := by
  simp [eqOutputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.project,
    SignalSelection.Matches, SignalMap.select, SignalSelection.prepend]

private def eqStateCorresponds (_ : eqCycleContract.state.Values)
    (_ : (ModuleStructure.primitive eq).State) : Prop := True

private theorem eqImplements : Contracts.Cycle.Implements (.primitive eq) eqCycleContract
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
      simp [eqOutputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, SignalSelection.prepend, eq]
  · rfl

def eqCertified : Contracts.Cycle.ModuleCycleCertified eq.ports where
  moduleStructure := .primitive eq
  cycleContract := eqCycleContract
  certification := {
    stateCorresponds := eqStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (eq.outputValues inputs state)
      (eq.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution eq,
    implements := eqImplements }
end Silean.Primitives
