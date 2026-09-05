import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.FullAdder.FullAdder
import Silean.Modules.HalfAdder.HalfAdderCertified
import Silean.Primitives.Or

namespace Silean.Modules.FullAdder

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-- The independently assembled full-adder hierarchy contains no behavioral
blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  ⟨rfl⟩

/-! ## Cycle certification -/

module_child_certifications childContracts for body where
  operands := HalfAdder.certification,
  carry := HalfAdder.certification,
  combineCarry := Primitives.orCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .sum => [.operands => HalfAdder.Rule.sum,
      .carry => HalfAdder.Rule.sum]
    | .carryOut => [.operands => HalfAdder.Rule.sum,
      .operands => HalfAdder.Rule.carry,
      .carry => HalfAdder.Rule.carry,
      .combineCarry => Primitives.OrRule.apply]
  state := []

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  child_contract_fact operandSumValue : (proposal.2 .operands).outputs .sum =
      HalfAdder.sumValue (inputs .left) (inputs .right) from
      (childMatch .operands).1 using HalfAdder.sum_of_evaluatesTo _ _ _ _
      unfolding body, wiring, context
  child_contract_fact operandCarryValue : (proposal.2 .operands).outputs .carry =
      HalfAdder.carryValue (inputs .left) (inputs .right) from
      (childMatch .operands).1 using HalfAdder.carry_of_evaluatesTo _ _ _ _
      unfolding body, wiring, context
  child_contract_fact finalSumValue : (proposal.2 .carry).outputs .sum =
      HalfAdder.sumValue ((proposal.2 .operands).outputs .sum) (inputs .carryIn) from
      (childMatch .carry).1 using HalfAdder.sum_of_evaluatesTo _ _ _ _
      unfolding body, wiring, context
  child_contract_fact secondCarryValue : (proposal.2 .carry).outputs .carry =
      HalfAdder.carryValue ((proposal.2 .operands).outputs .sum) (inputs .carryIn) from
      (childMatch .carry).1 using HalfAdder.carry_of_evaluatesTo _ _ _ _
      unfolding body, wiring, context
  have combinedCarryValue :=
    (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .combineCarry).1.1 Primitives.OrRule.apply)
  normalize_child_hyp combinedCarryValue unfolding body, wiring, context
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
        change carryOutRule.Holds inputs contractState proposal.outputs
        rw [carryOutRule_holds_iff]
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

/-! The full-adder wiring implements its contract for every family of child
structures implementing the two HalfAdder and OR boundary contracts. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

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
  (carryOutRule_holds_iff inputs state outputs).mp (evaluates.1 .carryOut)

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
