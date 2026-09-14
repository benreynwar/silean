import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.Constant.Constant
import Silean.Primitives.Or

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

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  child_contract_fact immediateIValue :
      (proposal.2 .immediateI).outputs .output =
        Modules.VectorLayout.apply immediateILayout (inputs .word) from
      (childMatch .immediateI).1 using
      Modules.VectorLayout.output_of_evaluatesTo 32 32 immediateILayout _ _ _ _
        unfolding body, wiring, context
  child_contract_fact immediateUValue :
      (proposal.2 .immediateU).outputs .output =
        Modules.VectorLayout.apply immediateULayout (inputs .word) from
      (childMatch .immediateU).1 using
      Modules.VectorLayout.output_of_evaluatesTo 32 32 immediateULayout _ _ _ _
        unfolding body, wiring, context
  child_contract_fact immediateSValue :
      (proposal.2 .immediateS).outputs .output =
        Modules.VectorLayout.apply immediateSLayout (inputs .word) from
      (childMatch .immediateS).1 using
      Modules.VectorLayout.output_of_evaluatesTo 32 32 immediateSLayout _ _ _ _
        unfolding body, wiring, context
  child_contract_fact immediateBValue :
      (proposal.2 .immediateB).outputs .output =
        Modules.VectorLayout.apply immediateBLayout (inputs .word) from
      (childMatch .immediateB).1 using
      Modules.VectorLayout.output_of_evaluatesTo 32 32 immediateBLayout _ _ _ _
        unfolding body, wiring, context

  have uSelectedValue : (proposal.2 .uSelected).outputs .output =
      (inputs .instr_lui || inputs .instr_auipc) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] using equation
  have iSelectedPartialValue : (proposal.2 .iSelectedPartial).outputs .output =
      (inputs .instr_jalr || inputs .is_lb_lh_lw_lbu_lhu) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelectedPartial).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] using equation
  have iSelectedValue : (proposal.2 .iSelected).outputs .output =
      selectedI (valuesOf inputs) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iSelected).1.1 .apply)
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, iSelectedPartialValue]
    rfl
  have lowerValidValue : (proposal.2 .lowerValid).outputs .output =
      (inputs .is_beq_bne_blt_bge_bltu_bgeu || inputs .is_sb_sh_sw) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .lowerValid).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] using equation
  have iOrLowerValidValue : (proposal.2 .iOrLowerValid).outputs .output =
      (selectedI (valuesOf inputs) ||
        (inputs .is_beq_bne_blt_bge_bltu_bgeu || inputs .is_sb_sh_sw)) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .iOrLowerValid).1.1 .apply)
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, iSelectedValue, lowerValidValue]
  have uOrLowerValidValue : (proposal.2 .uOrLowerValid).outputs .output =
      (selectedU (valuesOf inputs) || (selectedI (valuesOf inputs) ||
        (inputs .is_beq_bne_blt_bge_bltu_bgeu || inputs .is_sb_sh_sw))) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .uOrLowerValid).1.1 .apply)
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, uSelectedValue, iOrLowerValidValue]
    rfl
  have validValue : (proposal.2 .validGate).outputs .output =
      structuralValid (valuesOf inputs) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .validGate).1.1 .apply)
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, uOrLowerValidValue]
    rfl

  have zeroValue : (proposal.2 .zero).outputs .output = wordOfNat 0 := by
    have equation := Modules.Constant.output_of_evaluatesTo
      (.vector 32 .bit) (fun _ => false) _ _ _ _ (childMatch .zero).1
    rw [equation]
    funext index
    simp [wordOfNat]
  have selectSValue : (proposal.2 .selectS).outputs .result =
      bif inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectS).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, zeroValue, immediateSValue]
    rfl
  have selectBValue : (proposal.2 .selectB).outputs .result =
      bif inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (inputs .word)
      else bif inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectB).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, selectSValue, immediateBValue]
    rfl
  have selectIValue : (proposal.2 .selectI).outputs .result =
      bif selectedI (valuesOf inputs) then
        Modules.VectorLayout.apply immediateILayout (inputs .word)
      else bif inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (inputs .word)
      else bif inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectI).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, iSelectedValue, selectBValue, immediateIValue]
    rfl
  have selectUValue : (proposal.2 .selectU).outputs .result =
      bif selectedU (valuesOf inputs) then
        Modules.VectorLayout.apply immediateULayout (inputs .word)
      else bif selectedI (valuesOf inputs) then
        Modules.VectorLayout.apply immediateILayout (inputs .word)
      else bif inputs .is_beq_bne_blt_bge_bltu_bgeu then
        Modules.VectorLayout.apply immediateBLayout (inputs .word)
      else bif inputs .is_sb_sh_sw then
        Modules.VectorLayout.apply immediateSLayout (inputs .word)
      else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectU).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, uSelectedValue, selectIValue, immediateUValue]
    rfl
  have selectJValue : (proposal.2 .selectJ).outputs .result =
      structuralValue (valuesOf inputs) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectJ).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, selectUValue]
    rfl

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output
    · rw [show proposal.outputs .valid = (proposal.2 .validGate).outputs .output by
        exact boundary .valid]
      rw [validValue, structuralValid_eq]
      rfl
    · rw [show proposal.outputs .value = (proposal.2 .selectJ).outputs .result by
        exact boundary .value]
      rw [selectJValue, structuralValue_eq]
      rfl
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

/-- The concrete immediate decoder and every one of its descendants are free
of behavioral blackboxes. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Decoder.Immediate
