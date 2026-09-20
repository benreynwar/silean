import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.BinaryToOneHot.BinaryToOneHotTheorems
import Silean.Modules.CombMuxTree.CombMuxTreeTheorems
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Primitives.And

/-! Certification machinery for the authored register bank. -/

namespace Silean.Modules.RegisterBank

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

private abbrev decoder : Instance addressWidth readCount := .decoder
private abbrev decodeSplit : Instance addressWidth readCount := .decodeSplit
private abbrev gate (index : Fin (entryCount addressWidth)) :
    Instance addressWidth readCount := .gate index
private abbrev storage (index : Fin (entryCount addressWidth)) :
    Instance addressWidth readCount := .storage index
private abbrev combine : Instance addressWidth readCount := .combine
private abbrev readMux (port : Fin readCount) :
    Instance addressWidth readCount := .readMux port

module_child_certifications childContracts (element : SignalType)
    (addressWidth : Nat) (readCount : Nat)
    for body element addressWidth readCount where
  decoder := BinaryToOneHot.certification addressWidth,
  decodeSplit :=
    (Composition.SignalSplitter.vector
      (entryCount addressWidth) .bit).certified.certification,
  gate (_index : Fin (entryCount addressWidth)) :=
    Primitives.andCertified.certification,
  storage (_index : Fin (entryCount addressWidth)) :=
    EnabledRegister.certification element,
  combine := (entryCombiner element addressWidth).certified.certification,
  readMux (_port : Fin readCount) :=
    CombMuxTree.certification element addressWidth

private abbrev decoderOccurrence (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.decoder, BinaryToOneHot.Rule.apply⟩

private abbrev splitOccurrence (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.decodeSplit, Composition.SignalComponentRule.apply⟩

private abbrev gateOccurrence (element : SignalType)
    (addressWidth readCount : Nat)
    (index : Fin (entryCount addressWidth)) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.gate index, Primitives.AndRule.apply⟩

private abbrev storageOccurrence (element : SignalType)
    (addressWidth readCount : Nat)
    (index : Fin (entryCount addressWidth)) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.storage index, EnabledRegister.Rule.observe⟩

private abbrev combineOccurrence (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.combine, Composition.SignalComponentRule.apply⟩

private abbrev muxOccurrence (element : SignalType)
    (addressWidth readCount : Nat)
    (port : Fin readCount) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount)
      (childContracts element addressWidth readCount) :=
  ⟨.readMux port, CombMuxTree.Rule.apply⟩



module_rule_schedules derivedRuleSchedules (element : SignalType)
    (addressWidth : Nat) (readCount : Nat)
    for body element addressWidth readCount
    with childContracts element addressWidth readCount
    implementing cycleContract element addressWidth readCount where
  output
    | .read port => from ((Enumeration.fin (entryCount addressWidth)).values.map
        (storageOccurrence element addressWidth readCount) ++
      [combineOccurrence element addressWidth readCount,
        muxOccurrence element addressWidth readCount port])
  state := from ([decoderOccurrence element addressWidth readCount,
      splitOccurrence element addressWidth readCount] ++
    (Enumeration.fin (entryCount addressWidth)).values.map
      (gateOccurrence element addressWidth readCount) ++
    (Enumeration.fin (entryCount addressWidth)).values.map
      (storageOccurrence element addressWidth readCount) ++
    [combineOccurrence element addressWidth readCount])


section LayerCertification

variable (element : SignalType)
  (addressWidth readCount : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body element addressWidth readCount)
    (childContracts element addressWidth readCount))

def stateCorresponds
    (contractState : (stateMap element addressWidth).Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth readCount) layerChildren).State) : Prop :=
  ∀ index : Fin (entryCount addressWidth),
    (layerChildren (storage index)).certification.stateCorresponds
      (fun | .stored => contractState .entries index)
      (structuralState (storage index))

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth readCount) layerChildren).State) :
    ∃ contractState,
      stateCorresponds element addressWidth readCount layerChildren contractState structuralState := by
  let Property := fun index contractState =>
    (layerChildren (storage index)).certification.stateCorresponds contractState
      (structuralState (storage index))
  have available : ∀ index, ∃ contractState, Property index contractState := by
    intro index
    exact (layerChildren (storage index)).certification.hasCorrespondingState
      (structuralState (storage index))
  rcases (Enumeration.fin (entryCount addressWidth)).exists_pi Property available with
    ⟨states, corresponds⟩
  let contractState : (stateMap element addressWidth).Values := fun
    | .entries => fun index => states index .stored
  exact ⟨contractState, fun index => corresponds index⟩

private theorem implements :
    Contracts.Cycle.ImplementsSolutions (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth readCount) layerChildren)
      (cycleContract element addressWidth readCount)
      (stateCorresponds element addressWidth readCount layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have storageMatches (index : Fin (entryCount addressWidth)) :=
    childSolutionMatchesContract (body := body element addressWidth readCount)
      layerChildren hierStep satisfies (storage index)
      (fun | .stored => contractState .entries index) (corresponds index)
  have storageCurrent : ∀ index : Fin (entryCount addressWidth),
      (hierStep.children (storage index)).outputs .q =
        contractState .entries index := by
    intro index
    exact EnabledRegister.q_of_allowed (storageMatches index).allowed

  derive_empty_state_child_match decoderMatches for decoder
    in body element addressWidth readCount from layerChildren, hierStep, satisfies
  have decoderValue (index : Fin (entryCount addressWidth)) :
      (hierStep.children decoder).outputs .result index =
        BinaryToOneHot.oneHot addressWidth
          (hierStep.inputs .writeAddress) index := by
    have held := decoderMatches.ruleHolds BinaryToOneHot.Rule.apply
    have result := BinaryToOneHot.result_of_holds addressWidth _ _ _ held index
    rw [show (body element addressWidth readCount).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs decoder .value =
        hierStep.inputs .writeAddress by rfl] at result
    exact result

  derive_empty_state_child_match splitMatches for decodeSplit
    in body element addressWidth readCount from layerChildren, hierStep, satisfies
  have splitValue (index : Fin (entryCount addressWidth)) :
      (hierStep.children decodeSplit).outputs index =
        (hierStep.children decoder).outputs .result index := by
    have equal := (Composition.SignalSplitter.outputRule_holds_iff
      (Composition.SignalSplitter.vector (entryCount addressWidth) .bit) _ _ _).mp
      (splitMatches.ruleHolds Composition.SignalComponentRule.apply)
    exact congrFun equal index

  have gateValue (index : Fin (entryCount addressWidth)) :
      (hierStep.children (gate index)).outputs .output =
        (BinaryToOneHot.oneHot addressWidth
          (hierStep.inputs .writeAddress) index &&
          hierStep.inputs .writeEnable) := by
    derive_empty_state_child_match gateMatches for (gate index)
      in body element addressWidth readCount from layerChildren, hierStep, satisfies
    have held := gateMatches.ruleHolds Primitives.AndRule.apply
    change Primitives.andOutputRule.Holds _ SignalMap.emptyValues _ at held
    rw [Primitives.andOutputRule_holds_iff] at held
    rw [show (body element addressWidth readCount).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (gate index) .left =
          hierStep.inputs .writeEnable by rfl,
      show (body element addressWidth readCount).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (gate index) .right =
          (hierStep.children decodeSplit).outputs index by rfl,
      splitValue index, decoderValue index] at held
    exact held.trans (Bool.and_comm _ _)

  derive_empty_state_child_match combineMatches for combine
    in body element addressWidth readCount from layerChildren, hierStep, satisfies
  have combineValue : (hierStep.children combine).outputs .value =
      fun index => (hierStep.children (storage index)).outputs .q := by
    have equal := (Composition.SignalCombiner.outputRule_holds_iff
      (entryCombiner element addressWidth) _ _ _).mp
      (combineMatches.ruleHolds Composition.SignalComponentRule.apply)
    exact congrFun equal Composition.AggregatePort.value

  have muxValue (port : Fin readCount) :
      (hierStep.children (readMux port)).outputs .result =
      contractState .entries
        (BitVector.toIndex addressWidth
          (hierStep.inputs (.readAddress port))) := by
    derive_empty_state_child_match muxMatches for (readMux port)
      in body element addressWidth readCount from layerChildren, hierStep, satisfies
    have held := muxMatches.ruleHolds CombMuxTree.Rule.apply
    change (CombMuxTree.outputRule element addressWidth).Holds
      ((body element addressWidth readCount).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs (readMux port))
      SignalMap.emptyValues (hierStep.children (readMux port)).outputs at held
    rw [CombMuxTree.outputRule_holds_iff] at held
    rw [show (body element addressWidth readCount).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (readMux port) .values =
          (hierStep.children combine).outputs .value by rfl,
      show (body element addressWidth readCount).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs (readMux port) .index =
          hierStep.inputs (.readAddress port) by rfl] at held
    rw [held]
    unfold CombMuxTree.select
    change (hierStep.children combine).outputs .value
      (BitVector.toIndex addressWidth
        (hierStep.inputs (.readAddress port))) = _
    rw [combineValue]
    change (hierStep.children (storage (BitVector.toIndex addressWidth
      (hierStep.inputs (.readAddress port))))).outputs .q = _
    exact storageCurrent _

  let nextContractState : (stateMap element addressWidth).Values := fun
    | .entries => nextEntries addressWidth (hierStep.inputs .writeEnable)
        (hierStep.inputs .writeAddress) (hierStep.inputs .writeValue)
        (contractState .entries)
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | read port =>
        rw [readRule_holds_iff]
        exact (boundary (.readValue port)).trans (muxValue port)
    · rfl
  · intro index
    have nextCorresponds := (storageMatches index).nextCorresponds
    change (layerChildren (storage index)).certification.stateCorresponds
      (fun | .stored => (nextContractState .entries) index)
      (HierStep.nextState (layerChildren (storage index)).moduleStructure
        (hierStep.children (storage index)))
    have nextStateEq : (fun | .stored => (nextContractState .entries) index) =
        (childContracts element addressWidth readCount (storage index)).stateRule.apply
          ((body element addressWidth readCount).wiring.childInputValues
            hierStep.inputs hierStep.childOutputs (storage index))
          (fun | .stored => contractState .entries index) := by
      have storageNext :=
        EnabledRegister.next_stored_of_allowed (storageMatches index).allowed
      change (childContracts element addressWidth readCount
          (storage index)).stateRule.apply
            ((body element addressWidth readCount).wiring.childInputValues
              hierStep.inputs hierStep.childOutputs (storage index))
            (fun | .stored => contractState .entries index) .stored =
        bif ((body element addressWidth readCount).wiring.childInputValues
            hierStep.inputs hierStep.childOutputs (storage index)) .enable then
          ((body element addressWidth readCount).wiring.childInputValues
            hierStep.inputs hierStep.childOutputs (storage index)) .data
        else contractState .entries index at storageNext
      funext statePort
      cases statePort
      rw [storageNext]
      change (if hierStep.inputs .writeEnable &&
          decide (index = BitVector.toIndex addressWidth
            (hierStep.inputs .writeAddress)) then
          hierStep.inputs .writeValue else contractState .entries index) =
        bif (hierStep.children (gate index)).outputs .output then
          hierStep.inputs .writeValue
          else contractState .entries index
      rw [gateValue]
      have selected : decide (index = BitVector.toIndex addressWidth
          (hierStep.inputs .writeAddress)) =
          BinaryToOneHot.oneHot addressWidth
            (hierStep.inputs .writeAddress) index := by
        rw [BinaryToOneHot.oneHot_eq_decode]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, BinaryToOneHot.decode_eq_true_iff]
      rw [Bool.and_comm, selected]
      cases BinaryToOneHot.oneHot addressWidth
          (hierStep.inputs .writeAddress) index &&
          hierStep.inputs .writeEnable <;> rfl
    exact nextStateEq.symm ▸ nextCorresponds

end LayerCertification

/- The register-bank wiring implements its cycle contract using only the
public contracts of its decoder, storage, and selection children. -/
module_cycle_certification certification (element : SignalType)
    (addressWidth : Nat) (readCount : Nat)
    for moduleStructure element addressWidth readCount
    via body element addressWidth readCount
    with childContracts element addressWidth readCount
    implementing cycleContract element addressWidth readCount where
  schedules := derivedRuleSchedules element addressWidth readCount,
  structuralChildren := structuralChildren element addressWidth readCount,
  certifiedChildren := certifiedChildren element addressWidth readCount,
  structuresMatch := certifiedChildren_moduleStructure element addressWidth readCount,
  stateCorresponds := stateCorresponds element addressWidth readCount,
  stateCoverage := hasCorrespondingState element addressWidth readCount,
  implements := implements element addressWidth readCount

end Silean.Modules.RegisterBank
