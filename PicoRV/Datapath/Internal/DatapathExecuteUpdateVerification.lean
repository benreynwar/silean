import PicoRV.Datapath.DatapathBasicUpdates
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Datapath.ExecuteUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  target := Silean.Modules.Add.certification 32,
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    .falseBit => Silean.Primitives.ConstantRule.apply,
    .target => Silean.Modules.Add.Rule.apply,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let datapathInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)
  let updated := stateMap.unpack (hierStep.inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have decodedImmValue : hierStep.childOutputs .inputsFields .decoded_imm =
      datapathInputs.decoded_imm := by rw [inputsFieldsValue]; rfl
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have targetValue : hierStep.childOutputs .target .result =
      addWords (current .reg_pc) datapathInputs.decoded_imm := by
    have equation :=
      (Silean.Modules.Add.Behavior.of_allowed 32 (childMatch .target).allowed).result
    change hierStep.childOutputs .target .result = (Silean.Modules.Add.addBits 32
      (hierStep.childOutputs .currentFields .reg_pc)
      (hierStep.childOutputs .inputsFields .decoded_imm)
      (hierStep.childOutputs .falseBit .output)).1 at equation
    rw [currentFieldsValue, decodedImmValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        executeNextState datapathInputs current updated := by
    funext field
    cases field
    · change hierStep.childOutputs .updatedFields .reg_pc = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .reg_pc
    · change hierStep.childOutputs .updatedFields .reg_next_pc = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .reg_next_pc
    · change hierStep.childOutputs .updatedFields .reg_op1 = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .reg_op1
    · change hierStep.childOutputs .updatedFields .reg_op2 = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .reg_op2
    · exact targetValue
    · change hierStep.childOutputs .updatedFields .reg_sh = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .reg_sh
    · change hierStep.childOutputs .updatedFields .alu_out_q = _
      simpa [executeNextState, Silean.SignalMap.set] using congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (executeNextState datapathInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    simpa [StateUpdate.outputState, datapathInputs, current, updated] using resultValue
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.ExecuteUpdate
