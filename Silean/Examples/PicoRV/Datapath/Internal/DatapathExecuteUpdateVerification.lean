import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace Silean.Examples.PicoRV.Datapath.ExecuteUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  target := Modules.Add.certification 32,
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    .falseBit => Primitives.ConstantRule.apply,
    .target => Modules.Add.Rule.apply,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

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

  let datapathInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)
  let updated := stateMap.unpack (hierStep.inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .inputsFields =
      Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have decodedImmValue : hierStep.childOutputs .inputsFields .decoded_imm =
      datapathInputs.decoded_imm := by rw [inputsFieldsValue]; rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Primitives.ConstantRule.apply)
  have targetValue : hierStep.childOutputs .target .result =
      addWords (current .reg_pc) datapathInputs.decoded_imm := by
    have equation :=
      (Modules.Add.Behavior.of_allowed 32 (childMatch .target).allowed).result
    change hierStep.childOutputs .target .result = (Modules.Add.addBits 32
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
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .reg_pc
    · change hierStep.childOutputs .updatedFields .reg_next_pc = _
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .reg_next_pc
    · change hierStep.childOutputs .updatedFields .reg_op1 = _
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .reg_op1
    · change hierStep.childOutputs .updatedFields .reg_op2 = _
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .reg_op2
    · exact targetValue
    · change hierStep.childOutputs .updatedFields .reg_sh = _
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .reg_sh
    · change hierStep.childOutputs .updatedFields .alu_out_q = _
      simpa [executeNextState, SignalMap.set] using congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (executeNextState datapathInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Datapath.ExecuteUpdate
