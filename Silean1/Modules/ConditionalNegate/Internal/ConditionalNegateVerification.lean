import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.AddWithCarry.AddWithCarryDerived
import Silean.Modules.ConditionalNegate.Internal.ConditionalNegateArithmetic
import Silean.Modules.ConditionalNegate.Internal.ConditionalNegateStructure

/-! Internal schedules, structural certification, and authored-description
correspondence for `ConditionalNegate`. -/

namespace Silean.Modules.ConditionalNegate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat) for body width where
  broadcastNegate := (negateVector width).certified.certification,
  bitwiseXor := BitwiseXor.certification (.vector width .bit),
  zero := Constant.certification (.vector width .bit) (fun _ => false),
  add := AddWithCarry.certification width

module_rule_schedules derivedRuleSchedules (width : Nat) for body width
    with childContracts width implementing cycleContract width where
  output | .apply =>
    [.broadcastNegate => Composition.SignalComponentRule.apply,
      .bitwiseXor => BitwiseXor.Rule.apply,
      .zero => Primitives.ConstantRule.apply,
      .add => AddWithCarry.Rule.apply]
  state := []

private def broadcastInputs (width : Nat) (inputs : (ports width).inputs.Values) :
    (negateVector width).ports.inputs.Values := fun _ => inputs .negate

private def xorInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (broadcast : (negateVector width).ports.outputs.Values) :
    (BitwiseXor.ports (.vector width .bit)).inputs.Values
  | .left => inputs .value
  | .right => broadcast .value

private def addInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (xor : (BitwiseXor.ports (.vector width .bit)).outputs.Values)
    (zero : (Constant.ports (.vector width .bit)).outputs.Values) :
    (AddWithCarry.ports width).inputs.Values
  | .left => xor .result
  | .right => zero .output
  | .carryIn => inputs .negate

section LayerCertification

variable (width : Nat)
  (layerChildren : ChildStructures (body width) (childContracts width))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1

  derive_empty_state_child_matches childMatch for body width from
    layerChildren, hierStep, satisfies
  have broadcastEquation := (Composition.SignalCombiner.outputRule_holds_iff
    (negateVector width) _ SignalMap.emptyValues _).mp
      ((childMatch .broadcastNegate).ruleHolds
        Composition.SignalComponentRule.apply)
  have xorEquation := BitwiseXor.result_of_allowed (.vector width .bit)
    (childMatch .bitwiseXor).allowed
  change hierStep.childOutputs .bitwiseXor .result =
    (SignalType.vector width .bit).bitwiseXor
      ((body width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .bitwiseXor .left)
      ((body width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .bitwiseXor .right) at xorEquation
  have zeroEquation : hierStep.childOutputs .zero .output =
      (fun _ => false) :=
    (childMatch .zero).boundaryFact
      (property := fun _ outputs => outputs .output = (fun _ => false))
      (fun {step} allowed =>
        Constant.output_of_allowed (.vector width .bit) (fun _ => false)
          (step := step) allowed)
  have addResult := (childMatch .add).boundaryOutput
    (AddWithCarry.cycleContract.resultEquation width)

  have broadcastInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .broadcastNegate =
        broadcastInputs width hierStep.inputs := by
    funext index; rfl
  have xorInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .bitwiseXor =
        xorInputs width hierStep.inputs
          (hierStep.childOutputs .broadcastNegate) := by
    funext port; cases port <;> rfl
  have addInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .add =
        addInputs width hierStep.inputs
          (hierStep.childOutputs .bitwiseXor)
          (hierStep.childOutputs .zero) := by
    funext port; cases port <;> rfl
  rw [broadcastInputsEquation] at broadcastEquation
  rw [xorInputsEquation] at xorEquation
  rw [addInputsEquation] at addResult

  have broadcastValue : hierStep.childOutputs .broadcastNegate .value =
      fun _ => hierStep.inputs .negate := by
    rw [congrFun broadcastEquation .value]
    rfl
  have transformedValue : hierStep.childOutputs .bitwiseXor .result =
      fun index => Primitives.xorValue
        (hierStep.inputs .value index) (hierStep.inputs .negate) := by
    change hierStep.childOutputs .bitwiseXor .result =
      SignalType.bitwiseXor (.vector width .bit) (hierStep.inputs .value)
        (hierStep.childOutputs .broadcastNegate .value) at xorEquation
    rw [broadcastValue] at xorEquation
    exact xorEquation
  change hierStep.childOutputs .add .result =
    AddWithCarry.resultValue width (hierStep.childOutputs .bitwiseXor .result)
      (hierStep.childOutputs .zero .output)
      (hierStep.inputs .negate) at addResult
  rw [zeroEquation, transformedValue,
    Internal.add_result_eq_resultValue] at addResult

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .result =
        hierStep.childOutputs .add .result by exact boundary .result]
    exact addResult
  · funext label
    exact nomatch label

end LayerCertification

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

end Silean.Modules.ConditionalNegate

/-! ## Authored-description correspondence -/

namespace Silean.Modules.ConditionalNegate.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (width : Nat) :
    some (description width) = ofNaming (ConditionalNegate.naming width) := by
  simp [circuit_description, description, construction, AddWithCarry.place,
    Constant.place, negateVector, enumeration]
  rfl

theorem description_corresponds (width : Nat) :
    Corresponds (description width) (ConditionalNegate.naming width) :=
  ⟨same width⟩

open Authoring.CircuitDescription.Description

/-- The authored conditional-negation construction implements its cycle
contract. -/
theorem construction_correct (width : Nat) :
    ImplementsCycleContract (description width) (cycleContract width)
      (Naming.ports width) := by
  have corresponds := description_corresponds width
  unfold ConditionalNegate.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts width,
      wiring := wiring width })
    (children := structuralChildren width)
    corresponds (certification width)

end Silean.Modules.ConditionalNegate.Internal
