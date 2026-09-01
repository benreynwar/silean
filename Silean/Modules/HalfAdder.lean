import Silean.Contracts.Cycle.CycleLayerConstruction
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

@[reducible] private def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .sumGate => Primitives.xorCycleContract
  | .carryGate => Primitives.andCycleContract

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

/-! ## Cycle certification of the uninstantiated layer -/

private abbrev sumOccurrence : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.sumGate, Primitives.XorRule.apply⟩

private abbrev carryOccurrence : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.carryGate, Primitives.AndRule.apply⟩

@[simp] private theorem sumOccurrence_writes :
    sumOccurrence.writes = [.output] := rfl
@[simp] private theorem carryOccurrence_writes :
    carryOccurrence.writes = [.output] := rfl

private def sumSchedule : Contracts.Cycle.Certification.Layer.OutputSchedule body
    childContracts cycleContract .sum :=
  .call sumOccurrence
    (by intro input _; cases input <;> simp [cycleContract, sumRule,
      Contracts.Cycle.Certification.Layer.sourceAvailable, body, wiring, context, EndpointContext.moduleInput,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels])
    (by simp)
    (.done (by
      intro output member
      cases output with
      | sum => exact ⟨Primitives.XorRule.apply, by simp, by simp⟩
      | carry =>
        simp [cycleContract, sumRule, SignalSelection.labels,
          SignalMap.select] at member))

private def carrySchedule : Contracts.Cycle.Certification.Layer.OutputSchedule body
    childContracts cycleContract .carry :=
  .call carryOccurrence
    (by intro input _; cases input <;> simp [cycleContract, carryRule,
      Contracts.Cycle.Certification.Layer.sourceAvailable, body, wiring, context, EndpointContext.moduleInput,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels])
    (by simp)
    (.done (by
      intro output member
      cases output with
      | sum =>
        simp [cycleContract, carryRule, SignalSelection.labels,
          SignalMap.select] at member
      | carry => exact ⟨Primitives.AndRule.apply, by simp, by simp⟩))

private def stateSchedule : Contracts.Cycle.Certification.Layer.StateSchedule body
    childContracts :=
  .done (by
    intro child input member
    cases child <;>
      simp [childContracts,
        Primitives.xorCycleContract, Primitives.andCycleContract,
        Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

private def ruleSchedules : Contracts.Cycle.Certification.Layer.RuleSchedules body
    childContracts cycleContract where
  output
    | .sum => sumSchedule
    | .carry => carrySchedule
  state := stateSchedule

private theorem coversChildren :
    ruleSchedules.CoversChildren := by
  intro child rule
  right
  cases child with
  | sumGate =>
    change Primitives.XorRule at rule
    cases rule
    refine ⟨.sum, ?_⟩
    change sumOccurrence ∈ sumSchedule.finalAvailability
    simp [sumSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]
  | carryGate =>
    change Primitives.AndRule at rule
    cases rule
    refine ⟨.carry, ?_⟩
    change carryOccurrence ∈ carrySchedule.finalAvailability
    simp [carrySchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (certificationStructure layerChildren) cycleContract
      (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton (child : Instance) :
      Subsingleton (childContracts child).state.Values := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have sumMatches := childMatch .sumGate
  have carryMatches := childMatch .carryGate
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
      change sumRule.Holds inputs contractState _
      have gateValue := (Primitives.xorOutputRule_holds_iff _ _ _).mp
        (sumMatches.1.1 Primitives.XorRule.apply)
      rw [sumRule_holds_iff]
      rw [show proposal.outputs .sum = (proposal.2 .sumGate).outputs .output by
        exact boundary .sum]
      exact gateValue
    | carry =>
      change carryRule.Holds inputs contractState _
      have gateValue := (Primitives.andOutputRule_holds_iff _ _ _).mp
        (carryMatches.1.1 Primitives.AndRule.apply)
      rw [carryRule_holds_iff]
      rw [show proposal.outputs .carry = (proposal.2 .carryGate).outputs .output by
        exact boundary .carry]
      exact gateValue
  · rfl

end LayerCertification

/-- The half-adder wiring implements its contract for every pair of child
structures implementing the XOR and AND boundary contracts. -/
noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) implements

@[reducible] private def structuralChildren :
    (child : instancePorts.Name) → ModuleStructure (instancePorts.ports child)
  | .sumGate => .primitive Primitives.xor
  | .carryGate => .primitive Primitives.and

@[reducible] private noncomputable def certifiedChildren :
    (child : instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child)
  | .sumGate =>
      ⟨.primitive Primitives.xor, Primitives.xorCertified.certification⟩
  | .carryGate =>
      ⟨.primitive Primitives.and, Primitives.andCertified.certification⟩

def moduleStructure : ModuleStructure ports :=
  .composite body structuralChildren

/-- The half-adder hierarchy contains no behavioral blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  ⟨rfl⟩

/-- Instantiate the certified half-adder layer with concrete XOR and AND
primitive structures. -/
noncomputable def certifiedStructure :
    Contracts.Cycle.ModuleCycleCertifiedStructure cycleContract :=
  certifiedLayer.instantiate certifiedChildren

@[simp] theorem certifiedStructure_moduleStructure :
    certifiedStructure.moduleStructure = moduleStructure := by
  unfold certifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    moduleStructure
  change ModuleStructure.composite body (fun name =>
    (certifiedChildren name).moduleStructure) =
      ModuleStructure.composite body structuralChildren
  congr
  funext child
  cases child <;> rfl

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  (certifiedStructure.certification.transportStructure
    certifiedStructure_moduleStructure).bundle

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
