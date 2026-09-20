import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.AddSub.Internal.AddSubArithmetic
import Silean.Modules.AddSub.Internal.AddSubStructure
import Silean.Modules.Add.AddDerived

/-! Internal schedules and structural certification for `AddSub`. -/

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat) for body width where
  broadcastSubtract := (subtractVector width).certified.certification,
  bitwiseXor := BitwiseXor.certification (.vector width .bit),
  add := Add.certification width

module_rule_schedules derivedRuleSchedules (width : Nat) for body width
    with childContracts width implementing cycleContract width where
  output | .apply =>
    [.broadcastSubtract => Composition.SignalComponentRule.apply,
      .bitwiseXor => BitwiseXor.Rule.apply,
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
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1

  derive_empty_state_child_matches childMatch for body width from
    layerChildren, hierStep, satisfies
  have broadcastEquation := (Composition.SignalCombiner.outputRule_holds_iff
    (subtractVector width) _ SignalMap.emptyValues _).mp
      ((childMatch .broadcastSubtract).ruleHolds Composition.SignalComponentRule.apply)

  have xorEquation := BitwiseXor.result_of_allowed (.vector width .bit)
    (childMatch .bitwiseXor).allowed
  change hierStep.childOutputs .bitwiseXor .result =
    (SignalType.vector width .bit).bitwiseXor
      ((body width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .bitwiseXor .left)
      ((body width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .bitwiseXor .right) at xorEquation

  have addResult := (childMatch .add).boundaryOutput
    (Add.cycleContract.resultEquation width)
  have addCarry := (childMatch .add).boundaryOutput
    (Add.cycleContract.carryOutEquation width)

  have broadcastInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .broadcastSubtract =
        broadcastInputs width hierStep.inputs := by
    funext index; rfl
  have xorInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .bitwiseXor =
        xorInputs width hierStep.inputs
          (hierStep.childOutputs .broadcastSubtract) := by
    funext port; cases port <;> rfl
  have addInputsEquation : (body width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .add =
        addInputs width hierStep.inputs
          (hierStep.childOutputs .bitwiseXor) := by
    funext port; cases port <;> rfl
  rw [broadcastInputsEquation] at broadcastEquation
  rw [xorInputsEquation] at xorEquation
  rw [addInputsEquation] at addResult addCarry

  have broadcastValue : hierStep.childOutputs .broadcastSubtract .value =
      fun _ => hierStep.inputs .subtract := by
    rw [congrFun broadcastEquation .value]
    rfl
  have transformedRight : hierStep.childOutputs .bitwiseXor .result =
      fun index => Primitives.xorValue
        (hierStep.inputs .right index) (hierStep.inputs .subtract) := by
    change hierStep.childOutputs .bitwiseXor .result =
      SignalType.bitwiseXor (.vector width .bit) (hierStep.inputs .right)
        (hierStep.childOutputs .broadcastSubtract .value) at xorEquation
    rw [broadcastValue] at xorEquation
    exact xorEquation
  change hierStep.childOutputs .add .result =
    Add.resultValue width (hierStep.inputs .left)
      (hierStep.childOutputs .bitwiseXor .result)
      (hierStep.inputs .subtract) at addResult
  rw [← Add.Internal.addBits_result width (hierStep.inputs .left)
    (hierStep.childOutputs .bitwiseXor .result)
    (hierStep.inputs .subtract)] at addResult
  change hierStep.childOutputs .add .carryOut =
    Add.carryValue width (hierStep.inputs .left)
      (hierStep.childOutputs .bitwiseXor .result)
      (hierStep.inputs .subtract) at addCarry
  rw [← Add.Internal.addBits_carry width (hierStep.inputs .left)
    (hierStep.childOutputs .bitwiseXor .result)
    (hierStep.inputs .subtract)] at addCarry
  rw [transformedRight] at addResult addCarry
  rw [Internal.addBits_xorRight_eq_addSubBits] at addResult addCarry

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    constructor
    · rw [show hierStep.outputs .result =
          hierStep.childOutputs .add .result by exact boundary .result]
      exact addResult
    · rw [show hierStep.outputs .carryOut =
          hierStep.childOutputs .add .carryOut by exact boundary .carryOut]
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

/-! ## Authored-description correspondence -/

namespace Silean.Modules.AddSub.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (width : Nat) :
    some (description width) = ofNaming (AddSub.naming width) := by
  simp [circuit_description, description, construction, Add.place,
    AddSub.subtractVector, enumeration]
  rfl

theorem description_corresponds (width : Nat) :
    Corresponds (description width) (AddSub.naming width) :=
  ⟨same width⟩

open Authoring.CircuitDescription.Description

/-- The authored add/subtract construction implements its cycle contract. -/
theorem construction_correct (width : Nat) :
    ImplementsCycleContract (description width) (cycleContract width)
      (Naming.ports width) := by
  have corresponds := description_corresponds width
  unfold AddSub.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts width,
      wiring := wiring width })
    (children := structuralChildren width)
    corresponds (certification width)

end Silean.Modules.AddSub.Internal
