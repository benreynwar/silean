import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.AddSub.AddSub

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat) for body width where
  broadcastSubtract := (subtractVector width).certified.certification,
  transformRight := BitwiseXor.certification (.vector width .bit),
  add := Add.certification width

module_rule_schedules derivedRuleSchedules (width : Nat) for body width
    with childContracts width implementing cycleContract width where
  output | .apply =>
    [.broadcastSubtract => Composition.SignalComponentRule.apply,
      .transformRight => BitwiseXor.Rule.apply,
      .add => Add.Rule.apply]
  state := []

private def broadcastInputs (width : Nat) (inputs : (ports width).inputs.Values) :
    (subtractVector width).ports.inputs.Values := fun _ => inputs .subtract

private def xorInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (broadcast : (subtractVector width).ports.outputs.Values) :
    (BitwiseXor.ports (.vector width .bit)).inputs.Values
  | .left => inputs .right
  | .right => broadcast .value

private def addInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (xor : (BitwiseXor.ports (.vector width .bit)).outputs.Values) :
    (Add.ports width).inputs.Values
  | .left => inputs .left
  | .right => xor .result
  | .carryIn => inputs .subtract

section LayerCertification

variable (width : Nat)
  (layerChildren : ChildStructures (body width) (childContracts width))

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1

  have childStateSubsingleton (child : Instance) :
      Subsingleton (childContracts width child).state.Values := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have broadcastEvaluates := (childMatch .broadcastSubtract).1
  have broadcastEquation := (Composition.SignalCombiner.outputRule_holds_iff
    (subtractVector width) _ SignalMap.emptyValues _).mp
      (broadcastEvaluates.1 Composition.SignalComponentRule.apply)

  have xorEvaluates := (childMatch .transformRight).1
  have xorEquation := BitwiseXor.result_of_evaluatesTo (.vector width .bit)
    _ SignalMap.emptyValues _ _ xorEvaluates

  have addEvaluates := (childMatch .add).1
  have addResult := Add.result_of_evaluatesTo width
    _ SignalMap.emptyValues _ _ addEvaluates
  have addCarry := Add.carry_of_evaluatesTo width
    _ SignalMap.emptyValues _ _ addEvaluates

  have broadcastInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .broadcastSubtract = broadcastInputs width inputs := by
    funext index; rfl
  have xorInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .transformRight =
        xorInputs width inputs (proposal.2 .broadcastSubtract).outputs := by
    funext port; cases port <;> rfl
  have addInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .add =
        addInputs width inputs (proposal.2 .transformRight).outputs := by
    funext port; cases port <;> rfl
  rw [broadcastInputsEquation] at broadcastEquation
  rw [xorInputsEquation] at xorEquation
  rw [addInputsEquation] at addResult addCarry

  have broadcastValue : (proposal.2 .broadcastSubtract).outputs .value =
      fun _ => inputs .subtract := by
    rw [congrFun broadcastEquation .value]
    rfl
  have transformedRight : (proposal.2 .transformRight).outputs .result =
      fun index => Primitives.xorValue (inputs .right index) (inputs .subtract) := by
    change (proposal.2 .transformRight).outputs .result =
      SignalType.bitwiseXor (.vector width .bit) (inputs .right)
        ((proposal.2 .broadcastSubtract).outputs .value) at xorEquation
    rw [broadcastValue] at xorEquation
    exact xorEquation
  change (proposal.2 .add).outputs .result =
    (Add.addBits width (inputs .left) ((proposal.2 .transformRight).outputs .result)
      (inputs .subtract)).1 at addResult
  change (proposal.2 .add).outputs .carryOut =
    (Add.addBits width (inputs .left) ((proposal.2 .transformRight).outputs .result)
      (inputs .subtract)).2 at addCarry
  rw [transformedRight] at addResult addCarry
  rw [addBits_xorRight_eq_addSubBits] at addResult addCarry

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · rw [show proposal.outputs .result =
          (proposal.2 .add).outputs .result by exact boundary .result]
      exact addResult
    · rw [show proposal.outputs .carryOut =
          (proposal.2 .add).outputs .carryOut by exact boundary .carryOut]
      exact addCarry
  · funext label
    exact nomatch label

end LayerCertification

/- The add/subtract wiring implements its arithmetic contract for any
children satisfying the broadcast, XOR, and adder contracts. -/
module_cycle_certification certification (width : Nat)
    for moduleStructure width via body width
    with childContracts width implementing cycleContract width where
  schedules := derivedRuleSchedules width,
  structuralChildren := structuralChildren width,
  certifiedChildren := certifiedChildren width,
  structuresMatch := certifiedChildren_moduleStructure width,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements width

end Silean.Modules.AddSub
