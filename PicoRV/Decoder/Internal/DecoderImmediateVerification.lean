import PicoRV.Decoder.DecoderImmediate
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.Constant.Constant
import Silean.Primitives.Or

/-! Internal schedules and structural certification for immediate decoding. -/

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open PicoRV.Decoder
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  immediateI := Silean.Modules.VectorLayout.certification 32 32 immediateILayout,
  immediateU := Silean.Modules.VectorLayout.certification 32 32 immediateULayout,
  immediateS := Silean.Modules.VectorLayout.certification 32 32 immediateSLayout,
  immediateB := Silean.Modules.VectorLayout.certification 32 32 immediateBLayout,
  uSelected := Silean.Primitives.orCertified.certification,
  iSelectedPartial := Silean.Primitives.orCertified.certification,
  iSelected := Silean.Primitives.orCertified.certification,
  lowerValid := Silean.Primitives.orCertified.certification,
  iOrLowerValid := Silean.Primitives.orCertified.certification,
  uOrLowerValid := Silean.Primitives.orCertified.certification,
  validGate := Silean.Primitives.orCertified.certification,
  zero := Silean.Modules.Constant.certification (.vector 32 .bit) (fun _ => false),
  selectS := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectB := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectI := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectU := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectJ := Silean.Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.immediateI, .immediateU, .immediateS, .immediateB} =>
          Silean.Modules.VectorLayout.Rule.apply,
        {.uSelected, .iSelectedPartial, .lowerValid} => Silean.Primitives.OrRule.apply,
        .iSelected => Silean.Primitives.OrRule.apply,
        .iOrLowerValid => Silean.Primitives.OrRule.apply,
        .uOrLowerValid => Silean.Primitives.OrRule.apply,
        .validGate => Silean.Primitives.OrRule.apply,
        .zero => Silean.Primitives.ConstantRule.apply,
        .selectS => Silean.Modules.Mux.Rule.select,
        .selectB => Silean.Modules.Mux.Rule.select,
        .selectI => Silean.Modules.Mux.Rule.select,
        .selectU => Silean.Modules.Mux.Rule.select,
        .selectJ => Silean.Modules.Mux.Rule.select]
  state := []

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  have immediateIValue := Silean.Modules.VectorLayout.output_of_allowed 32 32
    immediateILayout (childMatch .immediateI).allowed
  normalize_child_hyp immediateIValue unfolding wiring, context
  have immediateUValue := Silean.Modules.VectorLayout.output_of_allowed 32 32
    immediateULayout (childMatch .immediateU).allowed
  normalize_child_hyp immediateUValue unfolding wiring, context
  have immediateSValue := Silean.Modules.VectorLayout.output_of_allowed 32 32
    immediateSLayout (childMatch .immediateS).allowed
  normalize_child_hyp immediateSValue unfolding wiring, context
  have immediateBValue := Silean.Modules.VectorLayout.output_of_allowed 32 32
    immediateBLayout (childMatch .immediateB).allowed
  normalize_child_hyp immediateBValue unfolding wiring, context

  have uSelectedValue := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uSelected).ruleHolds .apply)
  simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at uSelectedValue
  have iSelectedPartialValue := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelectedPartial).ruleHolds .apply)
  simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at iSelectedPartialValue
  have iSelectedValue : hierStep.childOutputs .iSelected .output =
      selectedI (valuesOf hierStep.inputs) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelected).ruleHolds .apply)
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact (equation.trans (apply₂_congr Bool.or iSelectedPartialValue rfl)).trans rfl
  have lowerValidValue := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .lowerValid).ruleHolds .apply)
  simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at lowerValidValue
  have iOrLowerValidValue : hierStep.childOutputs .iOrLowerValid .output =
      (selectedI (valuesOf hierStep.inputs) ||
        (hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu || hierStep.inputs .is_sb_sh_sw)) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iOrLowerValid).ruleHolds .apply)
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact equation.trans (apply₂_congr Bool.or iSelectedValue lowerValidValue)
  have uOrLowerValidValue : hierStep.childOutputs .uOrLowerValid .output =
      (selectedU (valuesOf hierStep.inputs) || (selectedI (valuesOf hierStep.inputs) ||
        (hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu || hierStep.inputs .is_sb_sh_sw))) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uOrLowerValid).ruleHolds .apply)
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact (equation.trans
      (apply₂_congr Bool.or uSelectedValue iOrLowerValidValue)).trans rfl
  have validValue : hierStep.childOutputs .validGate .output =
      structuralValid (valuesOf hierStep.inputs) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .validGate).ruleHolds .apply)
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact (equation.trans
      (apply₂_congr Bool.or rfl uOrLowerValidValue)).trans rfl

  have zeroValue : hierStep.childOutputs .zero .output = wordOfNat 0 := by
    have equation := Silean.Modules.Constant.output_of_allowed
      (.vector 32 .bit) (fun _ => false) (childMatch .zero).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| by
      funext index
      simp [wordOfNat]
  have selectSValue : hierStep.childOutputs .selectS .result =
      bif hierStep.inputs .is_sb_sh_sw then
        Silean.Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectS).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact equation.trans
      (bif_congr rfl immediateSValue zeroValue)
  have selectBValue : hierStep.childOutputs .selectB .result =
      bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Silean.Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Silean.Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectB).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact equation.trans
      (bif_congr rfl immediateBValue selectSValue)
  have selectIValue : hierStep.childOutputs .selectI .result =
      bif selectedI (valuesOf hierStep.inputs) then
        Silean.Modules.VectorLayout.apply immediateILayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Silean.Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Silean.Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectI).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact equation.trans
      (bif_congr iSelectedValue immediateIValue selectBValue)
  have selectUValue : hierStep.childOutputs .selectU .result =
      bif selectedU (valuesOf hierStep.inputs) then
        Silean.Modules.VectorLayout.apply immediateULayout (hierStep.inputs .word)
      else bif selectedI (valuesOf hierStep.inputs) then
        Silean.Modules.VectorLayout.apply immediateILayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Silean.Modules.VectorLayout.apply immediateBLayout (hierStep.inputs .word)
      else bif hierStep.inputs .is_sb_sh_sw then
        Silean.Modules.VectorLayout.apply immediateSLayout (hierStep.inputs .word)
      else wordOfNat 0 := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectU).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact equation.trans
      (bif_congr uSelectedValue immediateUValue selectIValue)
  have selectJValue : hierStep.childOutputs .selectJ .result =
      structuralValue (valuesOf hierStep.inputs) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit) (childMatch .selectJ).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    exact (equation.trans
      (bif_congr rfl rfl selectUValue)).trans rfl

  have boundary := satisfies.1
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Decoder.Immediate
