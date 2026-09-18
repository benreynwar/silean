import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.Constant.Constant
import Silean.Primitives.Or

/-! Internal schedules and structural certification for immediate decoding. -/

namespace Silean.Examples.PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  immediateI := Modules.VectorLayout.certification 32 32 immediateILayout,
  immediateU := Modules.VectorLayout.certification 32 32 immediateULayout,
  immediateS := Modules.VectorLayout.certification 32 32 immediateSLayout,
  immediateB := Modules.VectorLayout.certification 32 32 immediateBLayout,
  uSelected := Primitives.orCertified.certification,
  iSelectedPartial := Primitives.orCertified.certification,
  iSelected := Primitives.orCertified.certification,
  lowerValid := Primitives.orCertified.certification,
  iOrLowerValid := Primitives.orCertified.certification,
  uOrLowerValid := Primitives.orCertified.certification,
  validGate := Primitives.orCertified.certification,
  zero := Modules.Constant.certification (.vector 32 .bit) (fun _ => false),
  selectS := Modules.Mux.certification (.vector 32 .bit),
  selectB := Modules.Mux.certification (.vector 32 .bit),
  selectI := Modules.Mux.certification (.vector 32 .bit),
  selectU := Modules.Mux.certification (.vector 32 .bit),
  selectJ := Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.immediateI, .immediateU, .immediateS, .immediateB} =>
          Modules.VectorLayout.Rule.apply,
        {.uSelected, .iSelectedPartial, .lowerValid} => Primitives.OrRule.apply,
        .iSelected => Primitives.OrRule.apply,
        .iOrLowerValid => Primitives.OrRule.apply,
        .uOrLowerValid => Primitives.OrRule.apply,
        .validGate => Primitives.OrRule.apply,
        .zero => Primitives.ConstantRule.apply,
        .selectS => Modules.Mux.Rule.select,
        .selectB => Modules.Mux.Rule.select,
        .selectI => Modules.Mux.Rule.select,
        .selectU => Modules.Mux.Rule.select,
        .selectJ => Modules.Mux.Rule.select]
  state := []

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have immediateIValue := Modules.VectorLayout.output_of_allowed 32 32
    immediateILayout (childMatch .immediateI).allowed
  normalize_child_hyp immediateIValue unfolding wiring, context
  have immediateUValue := Modules.VectorLayout.output_of_allowed 32 32
    immediateULayout (childMatch .immediateU).allowed
  normalize_child_hyp immediateUValue unfolding wiring, context
  have immediateSValue := Modules.VectorLayout.output_of_allowed 32 32
    immediateSLayout (childMatch .immediateS).allowed
  normalize_child_hyp immediateSValue unfolding wiring, context
  have immediateBValue := Modules.VectorLayout.output_of_allowed 32 32
    immediateBLayout (childMatch .immediateB).allowed
  normalize_child_hyp immediateBValue unfolding wiring, context

  have uSelectedValue := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uSelected).ruleHolds .apply)
  simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at uSelectedValue
  have iSelectedPartialValue := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelectedPartial).ruleHolds .apply)
  simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at iSelectedPartialValue
  have iSelectedValue : hierStep.childOutputs .iSelected .output =
      selectedI (valuesOf hierStep.inputs) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelected).ruleHolds .apply)
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact (equation.trans (apply₂_congr Bool.or iSelectedPartialValue rfl)).trans rfl
  have lowerValidValue := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .lowerValid).ruleHolds .apply)
  simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at lowerValidValue
  have iOrLowerValidValue : hierStep.childOutputs .iOrLowerValid .output =
      (selectedI (valuesOf hierStep.inputs) ||
        (hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu || hierStep.inputs .is_sb_sh_sw)) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iOrLowerValid).ruleHolds .apply)
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact equation.trans (apply₂_congr Bool.or iSelectedValue lowerValidValue)
  have uOrLowerValidValue : hierStep.childOutputs .uOrLowerValid .output =
      (selectedU (valuesOf hierStep.inputs) || (selectedI (valuesOf hierStep.inputs) ||
        (hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu || hierStep.inputs .is_sb_sh_sw))) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uOrLowerValid).ruleHolds .apply)
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact (equation.trans
      (apply₂_congr Bool.or uSelectedValue iOrLowerValidValue)).trans rfl
  have validValue : hierStep.childOutputs .validGate .output =
      structuralValid (valuesOf hierStep.inputs) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .validGate).ruleHolds .apply)
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact (equation.trans
      (apply₂_congr Bool.or rfl uOrLowerValidValue)).trans rfl

  have zeroValue : hierStep.childOutputs .zero .output = wordOfNat 0 := by
    have equation := Modules.Constant.output_of_allowed
      (.vector 32 .bit) (fun _ => false) (childMatch .zero).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| by
      funext index
      simp [wordOfNat]
  have selectSValue : hierStep.childOutputs .selectS .result =
      bif hierStep.inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectS).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact equation.trans
      (bif_congr rfl immediateSValue zeroValue)
  have selectBValue : hierStep.childOutputs .selectB .result =
      bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectB).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact equation.trans
      (bif_congr rfl immediateBValue selectSValue)
  have selectIValue : hierStep.childOutputs .selectI .result =
      bif selectedI (valuesOf hierStep.inputs) then
        Modules.VectorLayout.apply immediateILayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectI).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact equation.trans
      (bif_congr iSelectedValue immediateIValue selectBValue)
  have selectUValue : hierStep.childOutputs .selectU .result =
      bif selectedU (valuesOf hierStep.inputs) then
        Modules.VectorLayout.apply immediateULayout (hierStep.inputs .word)
      else bif selectedI (valuesOf hierStep.inputs) then
        Modules.VectorLayout.apply immediateILayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectU).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact equation.trans
      (bif_congr uSelectedValue immediateUValue selectIValue)
  have selectJValue : hierStep.childOutputs .selectJ .result =
      structuralValue (valuesOf hierStep.inputs) := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectJ).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    exact (equation.trans
      (bif_congr rfl rfl selectUValue)).trans rfl

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    funext output
    cases output
    · exact (boundary .valid).trans
        (validValue.trans (structuralValid_eq _))
    · exact (boundary .value).trans
        (selectJValue.trans (structuralValue_eq _))
  · rfl

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Decoder.Immediate
