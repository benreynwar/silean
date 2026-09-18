import PicoRV.Datapath.DatapathBasicUpdates
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems

namespace PicoRV.Datapath.LoadRs2Update

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  lowFive := Silean.Modules.VectorLayout.certification 32 5 lowFiveLayout,
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .lowFive => Silean.Modules.VectorLayout.Rule.apply,
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
  let updated := stateMap.unpack (hierStep.inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by
      rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by
      rw [ProofSupport.splitValue_eq_unpack]
  have rs2Value : hierStep.childOutputs .inputsFields .cpuregs_rs2 =
      datapathInputs.cpuregs_rs2 := by
    rw [inputsFieldsValue]
    rfl
  have lowFiveValue : hierStep.childOutputs .lowFive .output =
      lowFiveBits datapathInputs.cpuregs_rs2 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 5 lowFiveLayout
      (childMatch .lowFive).allowed
    change hierStep.childOutputs .lowFive .output =
      Silean.Modules.VectorLayout.apply lowFiveLayout
        (hierStep.childOutputs .inputsFields .cpuregs_rs2) at equation
    exact equation.trans <| (congrArg
      (Silean.Modules.VectorLayout.apply lowFiveLayout) rs2Value).trans <| by
        rw [ProofSupport.lowFive_layout]

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = loadRs2NextState datapathInputs updated := by
    funext field
    cases field <;>
      change hierStep.childOutputs _ _ = _
    · simpa [loadRs2NextState, Silean.SignalMap.set] using
        congrFun updatedFieldsValue .reg_pc
    · simpa [loadRs2NextState, Silean.SignalMap.set] using
        congrFun updatedFieldsValue .reg_next_pc
    · simpa [loadRs2NextState, Silean.SignalMap.set] using
        congrFun updatedFieldsValue .reg_op1
    · exact rs2Value
    · simpa [loadRs2NextState, Silean.SignalMap.set] using
        congrFun updatedFieldsValue .reg_out
    · exact lowFiveValue
    · simpa [loadRs2NextState, Silean.SignalMap.set] using
        congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (loadRs2NextState datapathInputs updated) := by
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
    simpa [StateUpdate.outputState, datapathInputs, updated] using resultValue
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

end PicoRV.Datapath.LoadRs2Update
