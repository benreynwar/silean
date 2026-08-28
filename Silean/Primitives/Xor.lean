import Silean.Contracts.Cycle.CycleImplementation
import Silean.Primitives.PrimitivePorts

namespace Silean.Primitives

open Silean

def xorValue (left right : Bool) : Bool :=
  (left && !right) || (!left && right)

/-- Stateless one-bit XOR primitive. -/
@[reducible] def xor : Primitive where
  ports := binaryPorts
  localState := emptySignalMap
  outputReads := [.left, .right]
  outputValues := fun inputs _ => fun | .output => xorValue (inputs .left) (inputs .right)
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    funext port
    cases port
    simp [agrees .left (by simp), agrees .right (by simp)]

inductive XorRule | apply
deriving Enumeration

def xorOutputRule : Contracts.Cycle.CycleOutputRule xor.ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (xor.ports.inputs.select .right).prepend .left
  writesOutputs := xor.ports.outputs.select .output
  target | (left, (right, ())), _ => (xorValue left right, ())

def xorCycleContract : Contracts.Cycle.ModuleCycleContract xor.ports where
  state := emptySignalMap
  RuleName := XorRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, xorOutputRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty xor.ports
  outputCoverage := by rfl

@[simp] theorem xorOutputRule_holds_iff
    (inputs : xor.ports.inputs.Values)
    (state : xorCycleContract.state.Values)
    (outputs : xor.ports.outputs.Values) :
    xorOutputRule.Holds inputs state outputs ↔
      outputs .output = xorValue (inputs .left) (inputs .right) := by
  simp [xorOutputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.project,
    SignalSelection.Matches, SignalMap.select, SignalSelection.prepend]

theorem xor_eq_true_iff (left right : Bool) :
    xorValue left right = true ↔ left ≠ right := by
  cases left <;> cases right <;> simp [xorValue]

theorem xor_toNat_add_twice_and (left right : Bool) :
    (xorValue left right).toNat + 2 * (left && right).toNat =
      left.toNat + right.toNat := by
  cases left <;> cases right <;> decide

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
      simp [xorOutputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.project,
        SignalSelection.Matches, SignalMap.select, SignalSelection.prepend, xor]
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
