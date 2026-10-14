import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.AddSub.Internal.AddSubStructure
import Silean.Modules.Arithmetic.Internal.ArithmeticCorrectness

/-! Certification of the structural runtime-selectable arithmetic module. -/

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts
    (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool)
    for body leftWidth rightWidth leftSigned rightSigned extendOutput where
  leftExtension := VectorLayout.certification leftWidth
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
    (VectorLayout.extensionLayout leftSigned leftWidth
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput)),
  rightExtension := VectorLayout.certification rightWidth
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
    (VectorLayout.extensionLayout rightSigned rightWidth
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput)),
  addSub := AddSubWithCarry.certification
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput)

module_rule_schedules derivedRuleSchedules
    (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool)
    for body leftWidth rightWidth leftSigned rightSigned extendOutput
    with childContracts leftWidth rightWidth leftSigned rightSigned extendOutput
    implementing cycleContract leftWidth rightWidth leftSigned rightSigned
      extendOutput where
  output | .apply => [
    .leftExtension => VectorLayout.Rule.apply,
    .rightExtension => VectorLayout.Rule.apply,
    .addSub => AddSubWithCarry.Rule.apply]
  state := []

section LayerCertification

variable (leftWidth rightWidth : Nat)
  (leftSigned rightSigned extendOutput : Bool)
  (layerChildren : ChildStructures
    (body leftWidth rightWidth leftSigned rightSigned extendOutput)
    (childContracts leftWidth rightWidth leftSigned rightSigned extendOutput))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body leftWidth rightWidth leftSigned rightSigned extendOutput)
        layerChildren)
      (cycleContract leftWidth rightWidth leftSigned rightSigned extendOutput)
      (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for
    body leftWidth rightWidth leftSigned rightSigned extendOutput from
      layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  let width := Arithmetic.resultWidth leftWidth rightWidth extendOutput

  have leftEquation := VectorLayout.cycleContract.output leftWidth width
    (VectorLayout.extensionLayout leftSigned leftWidth width)
    (childMatch .leftExtension).allowed
  change hierStep.childOutputs .leftExtension .output =
    VectorLayout.apply
      (VectorLayout.extensionLayout leftSigned leftWidth width)
      (hierStep.inputs .left) at leftEquation
  have rightEquation := VectorLayout.cycleContract.output rightWidth width
    (VectorLayout.extensionLayout rightSigned rightWidth width)
    (childMatch .rightExtension).allowed
  change hierStep.childOutputs .rightExtension .output =
    VectorLayout.apply
      (VectorLayout.extensionLayout rightSigned rightWidth width)
      (hierStep.inputs .right) at rightEquation
  have addSubEquation := AddSubWithCarry.cycleContract.result width
    (childMatch .addSub).allowed
  change hierStep.childOutputs .addSub .result =
    (AddSubWithCarry.addSubBits width
      (hierStep.childOutputs .leftExtension .output)
      (hierStep.childOutputs .rightExtension .output)
      (hierStep.inputs .subtract)).1 at addSubEquation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result = resultValue leftWidth rightWidth
      leftSigned rightSigned extendOutput (hierStep.inputs .left)
        (hierStep.inputs .right) (hierStep.inputs .subtract)
    rw [show hierStep.outputs .result = hierStep.childOutputs .addSub .result
      by exact boundary .result]
    rw [addSubEquation, leftEquation, rightEquation]
    exact Arithmetic.Internal.addSubCircuitResult_eq_resultValue
      leftWidth rightWidth leftSigned rightSigned extendOutput
      (hierStep.inputs .left) (hierStep.inputs .right)
      (hierStep.inputs .subtract)
  · rfl

end LayerCertification

module_cycle_certification certification
    (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool)
    for moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput
    via body leftWidth rightWidth leftSigned rightSigned extendOutput
    with childContracts leftWidth rightWidth leftSigned rightSigned extendOutput
    implementing cycleContract leftWidth rightWidth leftSigned rightSigned
      extendOutput where
  schedules := derivedRuleSchedules leftWidth rightWidth leftSigned rightSigned
    extendOutput,
  structuralChildren := structuralChildren leftWidth rightWidth leftSigned
    rightSigned extendOutput,
  certifiedChildren := certifiedChildren leftWidth rightWidth leftSigned
    rightSigned extendOutput,
  structuresMatch := certifiedChildren_moduleStructure leftWidth rightWidth
    leftSigned rightSigned extendOutput,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements leftWidth rightWidth leftSigned rightSigned
    extendOutput

end Silean.Modules.AddSub
