import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Mux
import Silean.Modules.Mux.Internal.MuxStructure
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Primitives.Not

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  invertSelect := Primitives.notCertified.certification,
  chooseFalse := Mask.certification signalType,
  chooseTrue := Mask.certification signalType,
  combine := BitwiseOr.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .select => [.invertSelect => Primitives.NotRule.apply,
      .chooseFalse => Mask.Rule.apply,
      .chooseTrue => Mask.Rule.apply,
      .combine => BitwiseOr.Rule.apply]
  state := []

mutual
  private theorem muxIdentity : ∀ (signalType : SignalType)
      (whenFalse whenTrue : signalType.Denote) (select : Bool),
      signalType.bitwiseOr
          (signalType.mask whenFalse (!select))
          (signalType.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .bit, whenFalse, whenTrue, select => by
        cases select <;> cases whenFalse <;> cases whenTrue <;> rfl
    | .vector _ element, whenFalse, whenTrue, select => by
        cases select <;>
        funext index
        · exact muxIdentity element (whenFalse index) (whenTrue index) false
        · exact muxIdentity element (whenFalse index) (whenTrue index) true
    | .tuple fields, whenFalse, whenTrue, select =>
        muxFieldsIdentity fields whenFalse whenTrue select

  private theorem muxFieldsIdentity : ∀ (fields : SignalTypes)
      (whenFalse whenTrue : fields.Denote) (select : Bool),
      fields.bitwiseOr
          (fields.mask whenFalse (!select))
          (fields.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .nil, (), (), _ => rfl
    | .cons head tail, (falseHead, falseTail), (trueHead, trueTail), select => by
        cases select
        · apply Prod.ext
          · exact muxIdentity head falseHead trueHead false
          · exact muxFieldsIdentity tail falseTail trueTail false
        apply Prod.ext
        · exact muxIdentity head falseHead trueHead true
        · exact muxFieldsIdentity tail falseTail trueTail true
end

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : (child : (instancePorts signalType).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signalType) layerChildren

private def stateCorresponds
    (_ : (cycleContract signalType).state.Values)
    (_ : (certificationStructure signalType layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions (certificationStructure signalType layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body signalType from
    layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change (selectRule signalType).Holds hierStep.inputs contractState _
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .invertSelect).ruleHolds Primitives.NotRule.apply)
    have falseOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      ((childMatch .chooseFalse).ruleHolds Mask.Rule.apply)
    have trueOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      ((childMatch .chooseTrue).ruleHolds Mask.Rule.apply)
    have combineOutput := BitwiseOr.result_of_allowed signalType
      (childMatch .combine).allowed
    have boundaryResult := boundary .result
    change hierStep.outputs .result =
      hierStep.childOutputs .combine .result at boundaryResult
    change hierStep.childOutputs .chooseFalse .result =
      signalType.mask (hierStep.inputs .whenFalse)
        (hierStep.childOutputs .invertSelect .output) at falseOutput
    change hierStep.childOutputs .chooseTrue .result =
      signalType.mask (hierStep.inputs .whenTrue) (hierStep.inputs .select) at trueOutput
    change hierStep.childOutputs .combine .result =
      signalType.bitwiseOr (hierStep.childOutputs .chooseFalse .result)
        (hierStep.childOutputs .chooseTrue .result) at combineOutput
    rw [selectRule_holds_iff signalType]
    change hierStep.outputs .result =
      bif hierStep.inputs .select then hierStep.inputs .whenTrue
        else hierStep.inputs .whenFalse
    rw [boundaryResult, combineOutput, falseOutput, trueOutput, invertBit]
    exact muxIdentity signalType _ _ _
  · simp [cycleContract, stateRule,
      Contracts.Cycle.CycleStateRule.apply]

end LayerCertification

module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signalType

namespace Internal

/-- Proof bridge from the public structural boundary relation to the Mux's
contract behavior. -/
theorem result_of_realization (signalType : SignalType)
    {step : (moduleStructure signalType).Step}
    (realizes : (moduleStructure signalType).Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signalType).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signalType).allows_of_realizes
      contractState step corresponds realizes
  exact Mux.cycleContract.result signalType allowed

end Internal

end Silean.Modules.Mux

/-! ## Authored-description correspondence

The module-specific placement helpers and scoped logic notation used by
`Mux.lean` elaborate to the same four children and connections as the typed
production structure. Exact correspondence is `rfl`; the remaining proof
establishes name uniqueness across the erased description.

Descriptions preserve order and full `NamedModule` identities rather than
trusting module-key strings. Existing aggregate children have noncomputable
structures, so this comparison is noncomputable too; its equality is checked
by the kernel rather than by a separate netlist interpreter.
-/

namespace Silean.Modules.Mux.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType) :
    some (description signalType) = ofNaming (Mux.naming signalType) := by
  rfl

private theorem boundaryNamesUnique (signalType : SignalType) :
    (((description signalType).inputs.map (·.name)) ++
      ((description signalType).outputs.map (·.port.name))).Nodup :=
  of_decide_eq_true rfl

private theorem instanceNamesUnique (signalType : SignalType) :
    ((description signalType).children.map (·.name)).Nodup :=
  of_decide_eq_true rfl

theorem description_corresponds (signalType : SignalType) :
    Corresponds (description signalType) (Mux.naming signalType) :=
  ⟨same signalType⟩

open Authoring.CircuitDescription.Description

/-- Generated proof of the implementation-independent claim exposed by the
public mux facade. -/
theorem construction_correct (signalType : SignalType) :
    (description signalType).ImplementsCycleContract
      (cycleContract signalType) (Naming.ports signalType) := by
  have corresponds := description_corresponds signalType
  unfold Mux.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts signalType,
      wiring := wiring signalType })
    (children := structuralChildren signalType)
    corresponds (certification signalType)

end Silean.Modules.Mux.Internal
