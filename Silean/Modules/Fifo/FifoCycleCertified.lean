import Silean.Modules.Fifo.Fifo
import Silean.Modules.Fifo.FifoPointerControlCertified
import Silean.Modules.EnabledResetCounter.EnabledResetCounterCertified
import Silean.Modules.RegisterBank.RegisterBankCertified
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
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body element addressWidth) layerChildren)
      (cycleContract element addressWidth)
      (stateCorresponds element addressWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases corresponds with ⟨readCorresponds, writeCorresponds, storageCorresponds⟩
  have readMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .readCounter (fun | .stored => contractState .readPointer) readCorresponds
  have writeMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .writeCounter (fun | .stored => contractState .writePointer) writeCorresponds
  have storageMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies
      .storage (fun | .entries => contractState .entries) storageCorresponds
  have controlMatches :=
    letI : Subsingleton (childContracts element addressWidth .control).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .control SignalMap.emptyValues
  rcases readMatches with ⟨readEvaluates, readNextCorresponds⟩
  rcases writeMatches with ⟨writeEvaluates, writeNextCorresponds⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases controlMatches with ⟨controlEvaluates, _⟩
  have readCurrent : (proposal.2 .readCounter).outputs .value =
      contractState .readPointer :=
    (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (readEvaluates.1 EnabledResetCounter.Rule.observe)
  have writeCurrent : (proposal.2 .writeCounter).outputs .value =
      contractState .writePointer :=
    (EnabledResetCounter.outputRule_holds_iff (addressWidth + 1) _ _ _).mp
      (writeEvaluates.1 EnabledResetCounter.Rule.observe)
  have controlInputRead : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .readPointer =
      (proposal.2 .readCounter).outputs .value := rfl
  have controlInputWrite : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .writePointer =
      (proposal.2 .writeCounter).outputs .value := rfl
  have controlInputValid : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .inputValid =
      inputs .inputValid := rfl
  have controlOutputReady : ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .control .outputReady =
      inputs .outputReady := rfl
  have controlReadAddress : (proposal.2 .control).outputs .readAddress =
      Fifo.PointerControl.pointerAddress (contractState .readPointer) := by
    have held := (Fifo.PointerControl.readAddressRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.readAddress)
    rw [held, controlInputRead, readCurrent]
  have controlWriteAddress : (proposal.2 .control).outputs .writeAddress =
      Fifo.PointerControl.pointerAddress (contractState .writePointer) := by
    have held := (Fifo.PointerControl.writeAddressRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.writeAddress)
    rw [held, controlInputWrite, writeCurrent]
  have controlReady : (proposal.2 .control).outputs .inputReady =
      inputReady (contractState .readPointer) (contractState .writePointer) := by
    have held := (Fifo.PointerControl.inputReadyRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.inputReady)
    rw [held]
    simp only [inputReady]
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent]
  have controlValid : (proposal.2 .control).outputs .outputValid =
      outputValid (contractState .readPointer) (contractState .writePointer) := by
    have held := (Fifo.PointerControl.outputValidRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.outputValid)
    rw [held]
    simp only [outputValid]
    rw [controlInputRead, controlInputWrite, readCurrent, writeCurrent]
  have controlReadAdvance : (proposal.2 .control).outputs .readAdvance =
      readAdvance (contractState .readPointer) (contractState .writePointer)
        (inputs .outputReady) := by
    have held := (Fifo.PointerControl.readAdvanceRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.readAdvance)
    rw [held]
    simp only [readAdvance]
    rw [controlInputRead, controlInputWrite, controlOutputReady,
      readCurrent, writeCurrent]
  have controlWriteAdvance : (proposal.2 .control).outputs .writeAdvance =
      writeAdvance (contractState .readPointer) (contractState .writePointer)
        (inputs .inputValid) := by
    have held := (Fifo.PointerControl.writeAdvanceRule_holds_iff addressWidth _ _ _).mp
      (controlEvaluates.1 Fifo.PointerControl.Rule.writeAdvance)
    rw [held]
    simp only [writeAdvance]
    rw [controlInputRead, controlInputWrite, controlInputValid,
      readCurrent, writeCurrent]
  have storageRead : (proposal.2 .storage).outputs (.readValue 0) =
      outputData addressWidth (contractState .readPointer)
        (contractState .entries) := by
    have held := (RegisterBank.readRule_holds_iff element addressWidth 1 0 _ _ _).mp
      (storageEvaluates.1 (RegisterBank.Rule.read 0))
    rw [held]
    unfold outputData
    rw [show (ProposedValues.childInputs (body element addressWidth)
      (fun child => (layerChildren child).moduleStructure)
      inputs proposal.2 .storage) (.readAddress 0) =
        (proposal.2 .control).outputs .readAddress by rfl,
      controlReadAddress]
  let nextContractState : (stateMap element addressWidth).Values :=
    (stateRule element addressWidth).apply inputs contractState
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
        (proposal.2 .readCounter).nextState
      rw [show (fun | .stored => nextContractState .readPointer) =
          (childContracts element addressWidth .readCounter).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .readCounter)
            (fun | .stored => contractState .readPointer) by
        funext statePort
        cases statePort
        change nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
            (contractState .readPointer) (contractState .writePointer) =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            ((proposal.2 .control).outputs .readAdvance) (inputs .reset)
            (contractState .readPointer)
        rw [controlReadAdvance]
        rfl]
      exact readNextCorresponds
    · change (layerChildren .writeCounter).certification.stateCorresponds
        (fun | .stored => nextContractState .writePointer)
        (proposal.2 .writeCounter).nextState
      rw [show (fun | .stored => nextContractState .writePointer) =
          (childContracts element addressWidth .writeCounter).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .writeCounter)
            (fun | .stored => contractState .writePointer) by
        funext statePort
        cases statePort
        change nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
            (contractState .readPointer) (contractState .writePointer) =
          EnabledResetCounter.nextValue (addressWidth + 1) (zeroPointer addressWidth)
            ((proposal.2 .control).outputs .writeAdvance) (inputs .reset)
            (contractState .writePointer)
        rw [controlWriteAdvance]
        rfl]
      exact writeNextCorresponds
    · change (layerChildren .storage).certification.stateCorresponds
        (fun | .entries => nextContractState .entries)
        (proposal.2 .storage).nextState
      rw [show (fun | .entries => nextContractState .entries) =
          (childContracts element addressWidth .storage).stateRule.apply
            (ProposedValues.childInputs (body element addressWidth)
              (fun child => (layerChildren child).moduleStructure)
              inputs proposal.2 .storage)
            (fun | .entries => contractState .entries) by
        funext statePort
        cases statePort
        change nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
            (contractState .readPointer) (contractState .writePointer)
            (contractState .entries) =
          RegisterBank.nextEntries addressWidth
            ((proposal.2 .control).outputs .writeAdvance)
            ((proposal.2 .control).outputs .writeAddress)
            (inputs .inputData) (contractState .entries)
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
