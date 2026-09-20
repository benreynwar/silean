import Silean.Modules.Fifo.Fifo
import Silean.Modules.Fifo.FifoPointerControlTheorems
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.RegisterBank.RegisterBankTheorems
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo
open Contracts.Cycle.Certification.Layer
/-! ## Cycle certification

Everything below this point is proof construction. It connects the structure
shown at the beginning of the file to the exact cycle contract above; none of
it is consumed by FIRRTL generation. -/

module_child_certifications childContracts (element : SignalType)
    (addressWidth : Nat)
    for body element addressWidth where
  readCounter := EnabledResetCounter.certification (addressWidth + 1)
    (zeroPointer addressWidth),
  writeCounter := EnabledResetCounter.certification (addressWidth + 1)
    (zeroPointer addressWidth),
  control := Fifo.PointerControl.certification addressWidth,
  storage := RegisterBank.certification element addressWidth 1

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (addressWidth : Nat)
    for body element addressWidth
    with childContracts element addressWidth
    implementing cycleContract element addressWidth where
  output
    | .forward => [.readCounter => EnabledResetCounter.Rule.observe,
      .writeCounter => EnabledResetCounter.Rule.observe,
      .control => Fifo.PointerControl.Rule.outputValid,
      .control => Fifo.PointerControl.Rule.readAddress,
      .storage => RegisterBank.Rule.read 0]
    | .ready => [.readCounter => EnabledResetCounter.Rule.observe,
      .writeCounter => EnabledResetCounter.Rule.observe,
      .control => Fifo.PointerControl.Rule.inputReady]
  state := [.readCounter => EnabledResetCounter.Rule.observe,
    .writeCounter => EnabledResetCounter.Rule.observe,
    .control => Fifo.PointerControl.Rule.readAdvance,
    .control => Fifo.PointerControl.Rule.writeAdvance,
    .control => Fifo.PointerControl.Rule.writeAddress]

section LayerCertification

variable (element : SignalType)
  (addressWidth : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body element addressWidth) (childContracts element addressWidth))

private def stateCorresponds
    (contractState : (stateMap element addressWidth).Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth) layerChildren).State) : Prop :=
  (layerChildren .readCounter).certification.stateCorresponds
      (fun | .stored => contractState .readPointer) (structuralState .readCounter) ∧
  (layerChildren .writeCounter).certification.stateCorresponds
      (fun | .stored => contractState .writePointer) (structuralState .writeCounter) ∧
  (layerChildren .storage).certification.stateCorresponds
      (fun | .entries => contractState .entries) (structuralState .storage)

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth) layerChildren).State) :
    ∃ contractState,
      stateCorresponds element addressWidth layerChildren contractState structuralState := by
  rcases (layerChildren .readCounter).certification.hasCorrespondingState
      (structuralState .readCounter) with ⟨readState, readCorresponds⟩
  rcases (layerChildren .writeCounter).certification.hasCorrespondingState
      (structuralState .writeCounter) with ⟨writeState, writeCorresponds⟩
  rcases (layerChildren .storage).certification.hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  let contractState : (stateMap element addressWidth).Values := fun
    | .readPointer => readState .stored
    | .writePointer => writeState .stored
    | .entries => storageState .entries
  exact ⟨contractState, readCorresponds, writeCorresponds, storageCorresponds⟩

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body element addressWidth) layerChildren)
      (cycleContract element addressWidth)
      (stateCorresponds element addressWidth layerChildren) := by
  intro contractState hierStep corresponds satisfies
  rcases corresponds with ⟨readCorresponds, writeCorresponds, storageCorresponds⟩
  let readPointer : Pointer addressWidth :=
    fun index => contractState .readPointer index
  let writePointer : Pointer addressWidth :=
    fun index => contractState .writePointer index
  let entries : Entries element addressWidth :=
    fun index => contractState .entries index
  let reset : Bool := hierStep.inputs .reset
  let inputValid : Bool := hierStep.inputs .inputValid
  let inputData : element.Denote := hierStep.inputs .inputData
  let outputReady : Bool := hierStep.inputs .outputReady
  let controlReadAddressOutput : Fifo.PointerControl.Address addressWidth :=
    (hierStep.children .control).outputs .readAddress
  let controlWriteAddressOutput : Fifo.PointerControl.Address addressWidth :=
    (hierStep.children .control).outputs .writeAddress
  let controlReadyOutput : Bool :=
    (hierStep.children .control).outputs .inputReady
  let controlValidOutput : Bool :=
    (hierStep.children .control).outputs .outputValid
  let controlReadAdvanceOutput : Bool :=
    (hierStep.children .control).outputs .readAdvance
  let controlWriteAdvanceOutput : Bool :=
    (hierStep.children .control).outputs .writeAdvance
  have readMatches := childSolutionMatchesContract
    (body := body element addressWidth) layerChildren hierStep satisfies
      .readCounter (fun | .stored => contractState .readPointer) readCorresponds
  have writeMatches := childSolutionMatchesContract
    (body := body element addressWidth) layerChildren hierStep satisfies
      .writeCounter (fun | .stored => contractState .writePointer) writeCorresponds
  have storageMatches := childSolutionMatchesContract
    (body := body element addressWidth) layerChildren hierStep satisfies
      .storage (fun | .entries => contractState .entries) storageCorresponds
  derive_empty_state_child_match controlMatches for .control
    in body element addressWidth from layerChildren, hierStep, satisfies
  have readNextCorresponds := readMatches.nextCorresponds
  have writeNextCorresponds := writeMatches.nextCorresponds
  have storageNextCorresponds := storageMatches.nextCorresponds
  have readCurrent : (hierStep.children .readCounter).outputs .value =
      readPointer :=
    EnabledResetCounter.value_of_allowed readMatches.allowed
  have writeCurrent : (hierStep.children .writeCounter).outputs .value =
      writePointer :=
    EnabledResetCounter.value_of_allowed writeMatches.allowed
  have controlInputRead : (body element addressWidth).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .control .readPointer =
      (hierStep.children .readCounter).outputs .value := rfl
  have controlInputWrite : (body element addressWidth).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .control .writePointer =
      (hierStep.children .writeCounter).outputs .value := rfl
  have controlInputValid : (body element addressWidth).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .control .inputValid =
      inputValid := rfl
  have controlOutputReady : (body element addressWidth).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .control .outputReady =
      outputReady := rfl
  have controlBehavior :=
    Fifo.PointerControl.Behavior.of_allowed addressWidth controlMatches.allowed
  normalize_child_hyp controlBehavior
  have controlReadAddress : controlReadAddressOutput =
      Fifo.PointerControl.pointerAddress readPointer := by
    have equation := controlBehavior.readAddress
    change controlReadAddressOutput = _ at equation
    rw [controlInputRead, readCurrent] at equation
    exact equation
  have controlWriteAddress : controlWriteAddressOutput =
      Fifo.PointerControl.pointerAddress writePointer := by
    have equation := controlBehavior.writeAddress
    change controlWriteAddressOutput = _ at equation
    rw [controlInputWrite, writeCurrent] at equation
    exact equation
  have controlReady : controlReadyOutput =
      inputReady readPointer writePointer := by
    have equation := controlBehavior.inputReady
    change controlReadyOutput = _ at equation
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent] at equation
    exact equation
  have controlValid : controlValidOutput =
      outputValid readPointer writePointer := by
    have equation := controlBehavior.outputValid
    change controlValidOutput = _ at equation
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent] at equation
    exact equation
  have controlReadAdvance : controlReadAdvanceOutput =
      readAdvance readPointer writePointer
        outputReady := by
    have equation := controlBehavior.readAdvance
    change controlReadAdvanceOutput = _ at equation
    rw [controlInputRead, controlInputWrite, controlOutputReady,
      readCurrent, writeCurrent] at equation
    exact equation
  have controlWriteAdvance : controlWriteAdvanceOutput =
      writeAdvance readPointer writePointer
        inputValid := by
    have equation := controlBehavior.writeAdvance
    change controlWriteAdvanceOutput = _ at equation
    rw [controlInputRead, controlInputWrite, controlInputValid,
      readCurrent, writeCurrent] at equation
    exact equation
  have storageRead : (hierStep.children .storage).outputs (.readValue 0) =
      outputData addressWidth readPointer entries := by
    have held := RegisterBank.readValue_of_allowed storageMatches.allowed 0
    normalize_child_hyp held unfolding wiring, context
    unfold outputData
    exact held.trans (congrArg
      (fun address => entries
        (BitVector.toIndex addressWidth address)) controlReadAddress)
  let nextContractState : (stateMap element addressWidth).Values :=
    (stateRule element addressWidth).apply hierStep.inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      · rw [forwardRule_holds_iff]
        exact ⟨(satisfies.1 .outputValid).trans controlValid,
          (satisfies.1 .outputData).trans storageRead⟩
      · rw [readyRule_holds_iff]
        exact (satisfies.1 .inputReady).trans controlReady
    · rfl
  · refine ⟨?_, ?_, ?_⟩
    · change (layerChildren .readCounter).certification.stateCorresponds
        (fun | .stored => nextContractState .readPointer)
        (HierStep.nextState (layerChildren .readCounter).moduleStructure
          (hierStep.children .readCounter))
      rw [show (fun | .stored => nextContractState .readPointer) =
          (childContracts element addressWidth .readCounter).stateRule.apply
            ((body element addressWidth).wiring.childInputValues
              hierStep.inputs hierStep.childOutputs .readCounter)
            (fun | .stored => contractState .readPointer) by
        funext statePort
        cases statePort
        change nextReadPointer addressWidth reset outputReady
            readPointer writePointer =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            controlReadAdvanceOutput reset readPointer
        rw [controlReadAdvance]
        rfl]
      exact readNextCorresponds
    · change (layerChildren .writeCounter).certification.stateCorresponds
        (fun | .stored => nextContractState .writePointer)
        (HierStep.nextState (layerChildren .writeCounter).moduleStructure
          (hierStep.children .writeCounter))
      rw [show (fun | .stored => nextContractState .writePointer) =
          (childContracts element addressWidth .writeCounter).stateRule.apply
            ((body element addressWidth).wiring.childInputValues
              hierStep.inputs hierStep.childOutputs .writeCounter)
            (fun | .stored => contractState .writePointer) by
        funext statePort
        cases statePort
        change nextWritePointer addressWidth reset inputValid
            readPointer writePointer =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            controlWriteAdvanceOutput reset writePointer
        rw [controlWriteAdvance]
        rfl]
      exact writeNextCorresponds
    · change (layerChildren .storage).certification.stateCorresponds
        (fun | .entries => nextContractState .entries)
        (HierStep.nextState (layerChildren .storage).moduleStructure
          (hierStep.children .storage))
      rw [show (fun | .entries => nextContractState .entries) =
          (childContracts element addressWidth .storage).stateRule.apply
            ((body element addressWidth).wiring.childInputValues
              hierStep.inputs hierStep.childOutputs .storage)
            (fun | .entries => contractState .entries) by
        funext statePort
        cases statePort
        change nextEntries addressWidth inputValid inputData
            readPointer writePointer entries =
          RegisterBank.nextEntries addressWidth
            controlWriteAdvanceOutput controlWriteAddressOutput inputData entries
        rw [controlWriteAdvance, controlWriteAddress]
        rfl]
      exact storageNextCorresponds

end LayerCertification

/-! The FIFO wiring implements its cycle contract for any counters, control,
and storage hierarchy satisfying the declared child contracts. -/
module_cycle_certification certification (element : SignalType)
    (addressWidth : Nat)
    for moduleStructure element addressWidth
    via body element addressWidth
    with childContracts element addressWidth
    implementing cycleContract element addressWidth where
  schedules := derivedRuleSchedules element addressWidth,
  structuralChildren := structuralChildren element addressWidth,
  certifiedChildren := certifiedChildren element addressWidth,
  structuresMatch := certifiedChildren_moduleStructure element addressWidth,
  stateCorresponds := stateCorresponds element addressWidth,
  stateCoverage := hasCorrespondingState element addressWidth,
  implements := implements element addressWidth

end Silean.Modules.Fifo
