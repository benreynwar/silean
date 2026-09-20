import Silean.Authoring.CircuitDescription
import Silean.Contracts.Cycle.CycleImplementation
import Silean.Naming.PrimitiveNaming
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

private theorem implements : Contracts.Cycle.ImplementsSolutions (.primitive xor) xorCycleContract
    stateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change xorOutputRule.Holds inputs contractState outputs
    change outputs = xor.outputValues inputs structuralState ∧
      nextState = xor.nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def xorCertified : Contracts.Cycle.ModuleCycleCertified xor.ports where
  moduleStructure := .primitive xor
  cycleContract := xorCycleContract
  certification := {
    structural := xor.structuralCertification,
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp implements }

end Silean.Primitives

namespace Silean.Primitives.Xor

open Silean.Authoring.CircuitDescription

/-- Place a one-bit XOR gate in a circuit description. -/
def place (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "xor"
    Primitives.xorDesign fun
      | .left => left
      | .right => right
  pure (child .output)

end Silean.Primitives.Xor
