import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.AddSub.AddSub
import Silean.Modules.Add.AddTheorems

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

  have childStateSubsingleton (child : Instance) :
      Subsingleton (childContracts width child).state.Values := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact childSolutionMatchesContract_of_subsingletonState
      (body := body width) layerChildren hierStep satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have broadcastEquation := (Composition.SignalCombiner.outputRule_holds_iff
    (subtractVector width) _ SignalMap.emptyValues _).mp
      ((childMatch .broadcastSubtract).ruleHolds Composition.SignalComponentRule.apply)

  have xorEquation := (BitwiseXor.outputRule_holds_iff (.vector width .bit)
    _ SignalMap.emptyValues _).mp
      ((childMatch .bitwiseXor).ruleHolds Composition.BinaryLeafwise.Rule.apply)

  have addEquations := (Add.outputRule_holds_iff width
    _ SignalMap.emptyValues _).mp
      ((childMatch .add).ruleHolds Add.Rule.apply)
  have addResult := addEquations.1
  have addCarry := addEquations.2

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
    (Add.addBits width (hierStep.inputs .left)
      (hierStep.childOutputs .bitwiseXor .result)
      (hierStep.inputs .subtract)).1 at addResult
  change hierStep.childOutputs .add .carryOut =
    (Add.addBits width (hierStep.inputs .left)
      (hierStep.childOutputs .bitwiseXor .result)
      (hierStep.inputs .subtract)).2 at addCarry
  rw [transformedRight] at addResult addCarry
  rw [addBits_xorRight_eq_addSubBits] at addResult addCarry

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
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

namespace Silean.Modules.AddSub.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (width : Nat) :
    some (description width) = ofNaming (AddSub.naming width) := by
  simp only [circuit_description, description, construction, Add.place,
    AddSub.subtractVector]
  simp [circuit_description, enumeration]
  rfl

private theorem unique (width : Nat) : (description width).UniqueNames := by
  simp only [circuit_description, description, construction, Add.place,
    AddSub.subtractVector]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · subst child
    constructor
    · exact Naming.SignalAdapter.vectorCombiner_portNames_nodup width .bit
    · rw [List.map_map]
      change (Naming.SignalAdapter.combiner
          (.vector width .bit)).ports.inputs.names.Nodup
      exact (List.nodup_append.mp
        (Naming.SignalAdapter.vectorCombiner_portNames_nodup width .bit)).1
  · subst child
    constructor
    · exact BitwiseXor.Naming.portNames_nodup (.vector width .bit)
    · rw [show (BitwiseXor.Naming.namingWith (.vector width .bit)
          (.positional _)).ports = BitwiseXor.Naming.ports (.vector width .bit) by
        exact BitwiseXor.Naming.naming_ports (.vector width .bit)]
      exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Add.Naming.portNames_nodup width
    · rw [Add.Naming.naming_ports]
      exact of_decide_eq_true rfl

theorem corresponds (width : Nat) :
    Corresponds (description width) (AddSub.naming width) :=
  ⟨same width, unique width⟩

end Silean.Modules.AddSub.Description.Internal
