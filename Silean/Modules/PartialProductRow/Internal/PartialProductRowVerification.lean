import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.PartialProductRow.Internal.PartialProductRowStructure

namespace Silean.Modules.PartialProductRow

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts
    (multiplicandWidth : Nat) (multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    for body multiplicandWidth multiplierWidth row where
  mask := Mask.certification (.vector multiplicandWidth .bit),
  shift := VectorLayout.certification multiplicandWidth
    (multiplicandWidth + multiplierWidth)
    (VectorLayout.wideningLeftShiftLayout
      multiplicandWidth multiplierWidth row.castSucc)

module_rule_schedules derivedRuleSchedules
    (multiplicandWidth : Nat) (multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    for body multiplicandWidth multiplierWidth row
    with childContracts multiplicandWidth multiplierWidth row
    implementing cycleContract multiplicandWidth multiplierWidth row where
  output | .apply => [
    .mask => Mask.Rule.apply,
    .shift => VectorLayout.Rule.apply]
  state := []

section LayerCertification

variable (multiplicandWidth multiplierWidth : Nat) (row : Fin multiplierWidth)
  (layerChildren : ChildStructures
    (body multiplicandWidth multiplierWidth row)
    (childContracts multiplicandWidth multiplierWidth row))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body multiplicandWidth multiplierWidth row) layerChildren)
      (cycleContract multiplicandWidth multiplierWidth row)
      (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for
    body multiplicandWidth multiplierWidth row from
      layerChildren, hierStep, satisfies
  have maskResult := (Mask.outputRule_holds_iff
    (.vector multiplicandWidth .bit) _ SignalMap.emptyValues _).mp
      ((childMatch .mask).ruleHolds Mask.Rule.apply)
  have shiftResult := VectorLayout.cycleContract.output multiplicandWidth
    (multiplicandWidth + multiplierWidth)
    (VectorLayout.wideningLeftShiftLayout
      multiplicandWidth multiplierWidth row.castSucc)
    (childMatch .shift).allowed
  change hierStep.childOutputs .mask .result =
    (SignalType.vector multiplicandWidth .bit).mask
      (hierStep.inputs .multiplicand) (hierStep.inputs .select) at maskResult
  change hierStep.childOutputs .shift .output =
    VectorLayout.apply
      (VectorLayout.wideningLeftShiftLayout
        multiplicandWidth multiplierWidth row.castSucc)
      (hierStep.childOutputs .mask .result) at shiftResult
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result =
      resultValue multiplicandWidth multiplierWidth row
        (hierStep.inputs .multiplicand) (hierStep.inputs .select)
    rw [show hierStep.outputs .result =
        hierStep.childOutputs .shift .output by exact satisfies.1 .result]
    rw [shiftResult, maskResult]
    rw [VectorLayout.apply_wideningLeftShiftLayout_eq_ofNat]
    cases selected : hierStep.inputs .select <;>
      simp [resultValue, resultNat, SignalType.mask]
  · rfl

end LayerCertification

module_cycle_certification certification
    (multiplicandWidth : Nat) (multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    for moduleStructure multiplicandWidth multiplierWidth row
    via body multiplicandWidth multiplierWidth row
    with childContracts multiplicandWidth multiplierWidth row
    implementing cycleContract multiplicandWidth multiplierWidth row where
  schedules := derivedRuleSchedules multiplicandWidth multiplierWidth row,
  structuralChildren := structuralChildren multiplicandWidth multiplierWidth row,
  certifiedChildren := certifiedChildren multiplicandWidth multiplierWidth row,
  structuresMatch := certifiedChildren_moduleStructure
    multiplicandWidth multiplierWidth row,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements multiplicandWidth multiplierWidth row

end Silean.Modules.PartialProductRow

namespace Silean.Modules.PartialProductRow.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    some (description multiplicandWidth multiplierWidth row) =
      ofNaming (PartialProductRow.naming
        multiplicandWidth multiplierWidth row) := by
  simp only [circuit_description, description, construction,
    Mask.place, VectorLayout.placeWideningLeftShift]
  simp [circuit_description, enumeration]
  unfold moduleStructure naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Mask.design, Mask.designWith,
    VectorLayout.design, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [inputMap, outputMap, ports, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    Corresponds (description multiplicandWidth multiplierWidth row)
      (PartialProductRow.naming multiplicandWidth multiplierWidth row) :=
  ⟨same multiplicandWidth multiplierWidth row⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    ImplementsCycleContract
      (description multiplicandWidth multiplierWidth row)
      (cycleContract multiplicandWidth multiplierWidth row)
      (Naming.ports multiplicandWidth multiplierWidth) := by
  have corresponds := description_corresponds
    multiplicandWidth multiplierWidth row
  unfold PartialProductRow.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts multiplicandWidth multiplierWidth row,
      wiring := wiring multiplicandWidth multiplierWidth row })
    (children := structuralChildren multiplicandWidth multiplierWidth row)
    corresponds (certification multiplicandWidth multiplierWidth row)

end Silean.Modules.PartialProductRow.Internal
