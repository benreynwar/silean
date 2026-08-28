import Silean.Contracts.Cycle.CycleSchedule
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.Xor

namespace Silean.Modules.HalfAdder

open Silean

/-- A one-bit half adder. `sum` is XOR and `carry` is AND. -/
inductive Input | left | right
deriving Enumeration

inductive Output | sum | carry
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .left | .right => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .sum | .carry => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

def sumValue (left right : Bool) : Bool := Primitives.xorValue left right
def carryValue (left right : Bool) : Bool := left && right

inductive Rule | sum | carry
deriving Enumeration

def sumRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (inputMap.select .right).prepend .left
  writesOutputs := outputMap.select .sum
  target | (left, (right, ())), _ => (sumValue left right, ())

def carryRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit]) where
  readsInputs := (inputMap.select .right).prepend .left
  writesOutputs := outputMap.select .carry
  target | (left, (right, ())), _ => (carryValue left right, ())

def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .sum => ⟨_, sumRule⟩
    | .carry => ⟨_, carryRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty ports
  outputCoverage := by rfl

@[simp] theorem sumRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    sumRule.Holds inputs state outputs ↔
      outputs .sum = sumValue (inputs .left) (inputs .right) := by
  simp [sumRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

@[simp] theorem carryRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    carryRule.Holds inputs state outputs ↔
      outputs .carry = carryValue (inputs .left) (inputs .right) := by
  simp [carryRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

/-! ## Hardware structure -/

private inductive Instance
  /-- XOR gate producing the sum bit. -/
  | sumGate
  /-- AND gate producing the carry bit. -/
  | carryGate
deriving Enumeration

@[reducible] private def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .sumGate => Primitives.xor.ports
    | .carryGate => Primitives.and.ports

@[reducible] private def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    -- Each gate drives its corresponding boundary output.
    | .sum => context.instanceOutput .sumGate .output
    | .carry => context.instanceOutput .carryGate .output
  instanceInput
    -- Both gates observe the same two operand bits.
    | .sumGate, .left | .carryGate, .left => context.moduleInput .left
    | .sumGate, .right | .carryGate, .right => context.moduleInput .right

@[reducible] private def body : ModuleBody where
  context := context
  wiring := wiring

@[reducible] private def children : Contracts.Cycle.Certification.Children body
  | .sumGate => Primitives.xorCertified
  | .carryGate => Primitives.andCertified

@[reducible] private def childStructure := Contracts.Cycle.Certification.childStructure children

def moduleStructure : ModuleStructure ports :=
  Contracts.Cycle.Certification.moduleStructure body children

/-! ## Cycle certification -/

private abbrev sumOccurrence : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.sumGate, Primitives.XorRule.apply⟩

private abbrev carryOccurrence : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.carryGate, Primitives.AndRule.apply⟩

@[simp] private theorem sumOccurrence_writes : sumOccurrence.writes = [.output] := rfl
@[simp] private theorem carryOccurrence_writes : carryOccurrence.writes = [.output] := rfl

private def sumSchedule : Contracts.Cycle.Certification.OutputSchedule body children cycleContract .sum :=
  .call sumOccurrence
    (by intro input _; cases input <;> simp [cycleContract, sumRule,
      Contracts.Cycle.Certification.sourceAvailable, body, wiring, context, EndpointContext.moduleInput,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels])
    (by simp)
    (.done (by
      intro output member
      cases output with
      | sum => exact ⟨Primitives.XorRule.apply, by simp, by simp⟩
      | carry =>
        simp [cycleContract, sumRule, SignalSelection.labels,
          SignalMap.select] at member))

private def carrySchedule : Contracts.Cycle.Certification.OutputSchedule body children cycleContract .carry :=
  .call carryOccurrence
    (by intro input _; cases input <;> simp [cycleContract, carryRule,
      Contracts.Cycle.Certification.sourceAvailable, body, wiring, context, EndpointContext.moduleInput,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels])
    (by simp)
    (.done (by
      intro output member
      cases output with
      | sum =>
        simp [cycleContract, carryRule, SignalSelection.labels,
          SignalMap.select] at member
      | carry => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩))

private def stateSchedule : Contracts.Cycle.Certification.StateSchedule body children :=
  .done (by
    intro child input member
    cases child <;>
      simp [children, Primitives.xorCertified, Primitives.xorCycleContract,
        Primitives.andCertified, Primitives.andCycleContract,
        Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

private def ruleSchedules : Contracts.Cycle.Certification.RuleSchedules body children cycleContract where
  output
    | .sum => sumSchedule
    | .carry => carrySchedule
  state := stateSchedule

private theorem coversChildren : ruleSchedules.CoversChildren := by
  intro child rule
  cases child with
  | sumGate =>
    change Primitives.XorRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .sum
    change sumOccurrence ∈ sumSchedule.finalAvailability
    simp [sumSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | carryGate =>
    change Primitives.AndRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .carry
    change carryOccurrence ∈ carrySchedule.finalAvailability
    simp [carrySchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

private def gateInputs (inputs : ports.inputs.Values) :
    Primitives.binaryPorts.inputs.Values
  | .left => inputs .left
  | .right => inputs .right

private theorem hasStructuralResult (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal := by
  rcases Primitives.xorCertified.hasStructuralResult
      (gateInputs inputs) (currentState .sumGate) with ⟨sumProposal, sumSatisfies⟩
  rcases Primitives.andCertified.hasStructuralResult
      (gateInputs inputs) (currentState .carryGate) with ⟨carryProposal, carrySatisfies⟩
  let childProposals : (child : Instance) → ProposedValues (childStructure child)
    | .sumGate => sumProposal
    | .carryGate => carryProposal
  let outputs : ports.outputs.Values := fun
    | .sum => sumProposal.outputs .output
    | .carry => carryProposal.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | sumGate =>
      change Primitives.xorCertified.moduleStructure.IsSolution
        (ProposedValues.childInputs body childStructure inputs childProposals .sumGate)
        (currentState .sumGate) sumProposal
      rw [show ProposedValues.childInputs body childStructure inputs childProposals
          .sumGate = gateInputs inputs by funext port; cases port <;> rfl]
      exact sumSatisfies
    | carryGate =>
      change Primitives.andCertified.moduleStructure.IsSolution
        (ProposedValues.childInputs body childStructure inputs childProposals .carryGate)
        (currentState .carryGate) carryProposal
      rw [show ProposedValues.childInputs body childStructure inputs childProposals
          .carryGate = gateInputs inputs by funext port; cases port <;> rfl]
      exact carrySatisfies

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : moduleStructure.State) : Prop := True

private theorem implements : Contracts.Cycle.Implements moduleStructure cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have sumImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .sumGate SignalMap.emptyValues (by trivial)
  have carryImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .carryGate SignalMap.emptyValues (by trivial)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
      change sumRule.Holds inputs contractState _
      rcases sumImplements with ⟨_, evaluates, _⟩
      have gateValue := (Primitives.xorOutputRule_holds_iff _ _ _).mp
        (evaluates.1 Primitives.XorRule.apply)
      rw [sumRule_holds_iff]
      rw [show proposal.outputs .sum = (proposal.2 .sumGate).outputs .output by
        exact boundary .sum]
      exact gateValue
    | carry =>
      change carryRule.Holds inputs contractState _
      rcases carryImplements with ⟨_, evaluates, _⟩
      have gateValue := (Primitives.andOutputRule_holds_iff _ _ _).mp
        (evaluates.1 Primitives.AndRule.apply)
      rw [carryRule_holds_iff]
      rw [show proposal.outputs .carry = (proposal.2 .carryGate).outputs .output by
        exact boundary .carry]
      exact gateValue
  · rfl

private noncomputable def proofCertification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract where
  stateCorresponds := stateCorresponds
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := hasStructuralResult
  structuralResultUnique := hasAtMostOneSolution
  implements := implements

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  proofCertification.bundle

theorem sum_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .sum = sumValue (inputs .left) (inputs .right) :=
  (sumRule_holds_iff inputs state outputs).mp (evaluates.1 .sum)

theorem carry_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .carry = carryValue (inputs .left) (inputs .right) :=
  (carryRule_holds_iff inputs state outputs).mp (evaluates.1 .carry)

theorem sum_eq_true_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .sum = true ↔ inputs .left ≠ inputs .right := by
  rw [sum_of_evaluatesTo inputs state outputs nextState evaluates]
  exact Primitives.xor_eq_true_iff _ _

theorem carry_eq_true_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .carry = true ↔ inputs .left = true ∧ inputs .right = true := by
  rw [carry_of_evaluatesTo inputs state outputs nextState evaluates]
  cases inputs .left <;> cases inputs .right <;> simp [carryValue]

theorem numeric_value_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    (outputs .sum).toNat + 2 * (outputs .carry).toNat =
      (inputs .left).toNat + (inputs .right).toNat := by
  rw [sum_of_evaluatesTo inputs state outputs nextState evaluates,
    carry_of_evaluatesTo inputs state outputs nextState evaluates]
  exact Primitives.xor_toNat_add_twice_and _ _

end Silean.Modules.HalfAdder

namespace Silean.Modules.HalfAdder.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming Modules.HalfAdder.ports where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .sum => "sum" | .carry => "carry"⟩

def naming : ModuleNaming Modules.HalfAdder.moduleStructure := by
  unfold Modules.HalfAdder.moduleStructure
  exact .composite ⟨"half_adder", "structural", []⟩ ports
    (fun | .sumGate => "sum_gate" | .carryGate => "carry_gate")
    (fun
      | .sumGate => Silean.Naming.Primitive.xor
      | .carryGate => Silean.Naming.Primitive.and)

end Silean.Modules.HalfAdder.Naming
