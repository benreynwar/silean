import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace Silean.Examples.PicoRV.Datapath.ResetOverride

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  selectedFields := Modules.NamedTupleSplitter.certification stateMap,
  zeroWord := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  pc := Modules.Mux.certification (.vector 32 .bit),
  nextPc := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .selectedFields => Modules.NamedTupleSplitter.Rule.apply,
    .zeroWord => Primitives.ConstantRule.apply,
    {.pc, .nextPc} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralState (resetn : Bool) (selected : stateMap.Values) : stateMap.Values
  | .reg_pc => bif resetn then selected .reg_pc else wordOfNat 0
  | .reg_next_pc => bif resetn then selected .reg_next_pc else wordOfNat 0
  | field => selected field

theorem structuralState_eq_resetApplied (resetn : Bool)
    (selected : stateMap.Values) :
    structuralState resetn selected = resetApplied resetn selected := by
  cases resetn <;> funext field <;> cases field <;>
    simp [structuralState, resetApplied, SignalMap.set]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let selected := stateMap.unpack (hierStep.inputs .selected)
  have selectedFieldsValue : hierStep.childOutputs .selectedFields = selected := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .selectedFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .selectedFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .selected) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have zeroValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).ruleHolds Primitives.ConstantRule.apply)
  have pcValue : hierStep.childOutputs .pc .result =
      bif hierStep.inputs .resetn then selected .reg_pc else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .pc).allowed
    change hierStep.childOutputs .pc .result = bif hierStep.inputs .resetn
      then hierStep.childOutputs .selectedFields .reg_pc
      else hierStep.childOutputs .zeroWord .output at equation
    rw [selectedFieldsValue, zeroValue] at equation
    exact equation
  have nextPcValue : hierStep.childOutputs .nextPc .result =
      bif hierStep.inputs .resetn then selected .reg_next_pc else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .nextPc).allowed
    change hierStep.childOutputs .nextPc .result = bif hierStep.inputs .resetn
      then hierStep.childOutputs .selectedFields .reg_next_pc
      else hierStep.childOutputs .zeroWord .output at equation
    rw [selectedFieldsValue, zeroValue] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        structuralState (hierStep.inputs .resetn) selected := by
    funext field
    cases field
    · change hierStep.childOutputs .pc .result = _; exact pcValue
    · change hierStep.childOutputs .nextPc .result = _; exact nextPcValue
    · change hierStep.childOutputs .selectedFields .reg_op1 = _
      exact congrFun selectedFieldsValue .reg_op1
    · change hierStep.childOutputs .selectedFields .reg_op2 = _
      exact congrFun selectedFieldsValue .reg_op2
    · change hierStep.childOutputs .selectedFields .reg_out = _
      exact congrFun selectedFieldsValue .reg_out
    · change hierStep.childOutputs .selectedFields .reg_sh = _
      exact congrFun selectedFieldsValue .reg_sh
    · change hierStep.childOutputs .selectedFields .alu_out_q = _
      exact congrFun selectedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (structuralState (hierStep.inputs .resetn) selected) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    rw [resultValue, structuralState_eq_resetApplied]
    rfl
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Datapath.ResetOverride
