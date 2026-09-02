import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.HalfAdder
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Or

namespace Silean.Modules.FullAdder

open Silean
open Contracts.Cycle.Certification.Layer

/-! A one-bit full adder. Its contract states the direct three-input Boolean
behavior; the hardware implementation below is the standard composition of
two half adders and one OR gate. -/

inductive Input
  | left
  | right
  | carryIn
deriving Enumeration

inductive Output
  | sum
  | carryOut
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .left | .right | .carryIn => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .sum | .carryOut => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

/-- Low bit of the sum of three input bits. -/
def sumValue (left right carryIn : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carryIn

/-- High bit of the sum of three input bits. -/
def carryValue (left right carryIn : Bool) : Bool :=
  (left && right) || (left && carryIn) || (right && carryIn)

inductive Rule
  | sum
  | carryOut
deriving Enumeration

def sumRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    (.ofLists [.bit, .bit, .bit] [.bit]) where
  readsInputs := ((inputMap.select .carryIn).prepend .right).prepend .left
  writesOutputs := outputMap.select .sum
  target | (left, (right, (carryIn, ()))), _ => (sumValue left right carryIn, ())

def carryRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    (.ofLists [.bit, .bit, .bit] [.bit]) where
  readsInputs := ((inputMap.select .carryIn).prepend .right).prepend .left
  writesOutputs := outputMap.select .carryOut
  target | (left, (right, (carryIn, ()))), _ => (carryValue left right carryIn, ())

def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .sum => ⟨_, sumRule⟩
    | .carryOut => ⟨_, carryRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty ports
  outputCoverage := by rfl

@[simp] theorem sumRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    sumRule.Holds inputs state outputs ↔
      outputs .sum = sumValue (inputs .left) (inputs .right) (inputs .carryIn) := by
  simp [sumRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

@[simp] theorem carryRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    carryRule.Holds inputs state outputs ↔
      outputs .carryOut = carryValue (inputs .left) (inputs .right) (inputs .carryIn) := by
  simp [carryRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

/-! ## Hardware structure -/

private inductive Instance
  /-- Adds the two operand bits. -/
  | operands
  /-- Adds carry-in to the operands' partial sum. -/
  | carry
  /-- Combines the two mutually exclusive carry candidates. -/
  | combineCarry
deriving Enumeration

@[reducible] private def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .operands | .carry => HalfAdder.ports
    | .combineCarry => Primitives.or.ports

@[reducible] private def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    -- The second half adder produces the final sum.
    | .sum => context.instanceOutput .carry .sum
    -- The OR gate combines carry from either addition stage.
    | .carryOut => context.instanceOutput .combineCarry .output
  instanceInput
    -- First add the two operand bits.
    | .operands, .left => context.moduleInput .left
    | .operands, .right => context.moduleInput .right
    -- Then add carry-in to their partial sum.
    | .carry, .left => context.instanceOutput .operands .sum
    | .carry, .right => context.moduleInput .carryIn
    -- Either half-adder carry produces carry-out.
    | .combineCarry, .left => context.instanceOutput .operands .carry
    | .combineCarry, .right => context.instanceOutput .carry .carry

@[reducible] private def body : ModuleBody := ⟨context, wiring⟩

@[reducible] private def childContracts :
    Contracts.Cycle.ChildCycleContracts body
  | .operands | .carry => HalfAdder.cycleContract
  | .combineCarry => Primitives.orCycleContract

@[reducible] private noncomputable def certifiedChildren :
    (child : instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child)
  | .operands | .carry =>
      ⟨HalfAdder.moduleStructure, HalfAdder.certified.certification⟩
  | .combineCarry =>
      ⟨.primitive Primitives.or, Primitives.orCertified.certification⟩

@[reducible] private def structuralChildren :
    (child : instancePorts.Name) → ModuleStructure (instancePorts.ports child)
  | .operands | .carry => HalfAdder.moduleStructure
  | .combineCarry => .primitive Primitives.or

/-- The standard two-half-adder full-adder hierarchy. -/
def moduleStructure : ModuleStructure ports :=
  .composite body structuralChildren

/-- The independently assembled full-adder hierarchy contains no behavioral
blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  ⟨rfl⟩

/-! ## Cycle certification -/

private abbrev operandSum : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.operands, HalfAdder.Rule.sum⟩

private abbrev operandCarry : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.operands, HalfAdder.Rule.carry⟩

private abbrev finalSum : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.carry, HalfAdder.Rule.sum⟩

private abbrev secondCarry : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.carry, HalfAdder.Rule.carry⟩

private abbrev combinedCarry : Contracts.Cycle.Certification.Layer.RuleOccurrence
    body childContracts :=
  ⟨.combineCarry, Primitives.OrRule.apply⟩

private def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    body childContracts cycleContract where
  output
    | .sum => [operandSum, finalSum]
    | .carryOut => [operandSum, operandCarry, secondCarry, combinedCarry]
  state := []

private def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules
private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

attribute [local simp] body wiring

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  letI operandsStateSubsingleton :
      Subsingleton ((childContracts .operands).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  letI carryStateSubsingleton :
      Subsingleton ((childContracts .carry).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  letI combinedCarryStateSubsingleton :
      Subsingleton ((childContracts .combineCarry).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have operandsMatch :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
        .operands SignalMap.emptyValues
  have carryMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
        .carry SignalMap.emptyValues
  have combinedMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
        .combineCarry SignalMap.emptyValues
  have operandsEvaluate := operandsMatch.1
  have carryEvaluates := carryMatches.1
  have combinedEvaluates := combinedMatches.1
  have operandSumValue : (proposal.2 .operands).outputs .sum =
      HalfAdder.sumValue (inputs .left) (inputs .right) := by
    normalize_child_contract
      HalfAdder.sum_of_evaluatesTo _ _ _ _ operandsEvaluate
  have operandCarryValue : (proposal.2 .operands).outputs .carry =
      HalfAdder.carryValue (inputs .left) (inputs .right) := by
    normalize_child_contract
      HalfAdder.carry_of_evaluatesTo _ _ _ _ operandsEvaluate
  have finalSumValue : (proposal.2 .carry).outputs .sum =
      HalfAdder.sumValue ((proposal.2 .operands).outputs .sum) (inputs .carryIn) := by
    normalize_child_contract
      HalfAdder.sum_of_evaluatesTo _ _ _ _ carryEvaluates
  have secondCarryValue : (proposal.2 .carry).outputs .carry =
      HalfAdder.carryValue ((proposal.2 .operands).outputs .sum) (inputs .carryIn) := by
    normalize_child_contract
      HalfAdder.carry_of_evaluatesTo _ _ _ _ carryEvaluates
  have combinedCarryValue : (proposal.2 .combineCarry).outputs .output =
      ((proposal.2 .operands).outputs .carry || (proposal.2 .carry).outputs .carry) := by
    normalize_child_contract
        (Primitives.orOutputRule_holds_iff _ _ _).mp
          (combinedEvaluates.1 Primitives.OrRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule with
    | sum =>
        change sumRule.Holds inputs contractState proposal.outputs
        rw [sumRule_holds_iff]
        rw [show proposal.outputs .sum = (proposal.2 .carry).outputs .sum by
          exact boundary .sum]
        change (proposal.2 .carry).outputs .sum = _
        rw [finalSumValue]
        change HalfAdder.sumValue (proposal.2 .operands |>.outputs .sum)
          (inputs .carryIn) = _
        rw [operandSumValue]
        rfl
    | carryOut =>
        change carryRule.Holds inputs contractState proposal.outputs
        rw [carryRule_holds_iff]
        rw [show proposal.outputs .carryOut = (proposal.2 .combineCarry).outputs .output by
          exact boundary .carryOut]
        change (proposal.2 .combineCarry).outputs .output = _
        rw [combinedCarryValue]
        change ((proposal.2 .operands).outputs .carry ||
          (proposal.2 .carry).outputs .carry) = _
        rw [operandCarryValue, secondCarryValue]
        change (HalfAdder.carryValue (inputs .left) (inputs .right) ||
          HalfAdder.carryValue (proposal.2 .operands |>.outputs .sum)
            (inputs .carryIn)) = _
        rw [operandSumValue]
        cases inputs .left <;> cases inputs .right <;> cases inputs .carryIn <;>
          decide
  · rfl

end LayerCertification

/-- The full-adder wiring implements its contract for every family of child
structures implementing the two HalfAdder and OR boundary contracts. -/
noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) implements

noncomputable def certifiedStructure :
    Contracts.Cycle.ModuleCycleCertifiedStructure cycleContract :=
  certifiedLayer.instantiate certifiedChildren

@[simp] theorem certifiedStructure_moduleStructure :
    certifiedStructure.moduleStructure = moduleStructure := by
  unfold certifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    moduleStructure
  change ModuleStructure.composite body (fun child =>
    (certifiedChildren child).moduleStructure) =
      ModuleStructure.composite body structuralChildren
  congr
  funext child
  cases child <;> rfl

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedStructure.certification.transportStructure
    certifiedStructure_moduleStructure

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_moduleStructure : certified.moduleStructure = moduleStructure := rfl
@[simp] theorem certified_cycleContract : certified.cycleContract = cycleContract := rfl

theorem sum_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .sum = sumValue (inputs .left) (inputs .right) (inputs .carryIn) :=
  (sumRule_holds_iff inputs state outputs).mp (evaluates.1 .sum)

theorem carry_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut = carryValue (inputs .left) (inputs .right) (inputs .carryIn) :=
  (carryRule_holds_iff inputs state outputs).mp (evaluates.1 .carryOut)

/-- The Boolean full-adder functions encode the natural-number sum of their inputs. -/
theorem numeric_value (left right carryIn : Bool) :
    (sumValue left right carryIn).toNat + 2 * (carryValue left right carryIn).toNat =
      left.toNat + right.toNat + carryIn.toNat := by
  cases left <;> cases right <;> cases carryIn <;> decide

/-- The two output bits encode the natural-number sum of the three input bits. -/
theorem numeric_value_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    (outputs .sum).toNat + 2 * (outputs .carryOut).toNat =
      (inputs .left).toNat + (inputs .right).toNat + (inputs .carryIn).toNat := by
  rw [sum_of_evaluatesTo inputs state outputs nextState evaluates,
    carry_of_evaluatesTo inputs state outputs nextState evaluates]
  exact numeric_value (inputs .left) (inputs .right) (inputs .carryIn)

end Silean.Modules.FullAdder

namespace Silean.Modules.FullAdder.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming Modules.FullAdder.ports where
  inputs := ⟨fun | .left => "left" | .right => "right" | .carryIn => "carry_in"⟩
  outputs := ⟨fun | .sum => "sum" | .carryOut => "carry_out"⟩

def naming : ModuleNaming Modules.FullAdder.moduleStructure := by
  unfold Modules.FullAdder.moduleStructure
  exact .composite ⟨"full_adder", "structural", []⟩ ports
    (fun
      | .operands => "operands"
      | .carry => "carry"
      | .combineCarry => "combine_carry")
    (fun
      | .operands | .carry => HalfAdder.Naming.naming
      | .combineCarry => Silean.Naming.Primitive.or)

end Silean.Modules.FullAdder.Naming
