import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.BinaryToOneHot
import Silean.Modules.CombMuxTree
import Silean.Modules.EnabledRegister.EnabledRegisterCertified
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Primitives.And

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
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.Layer.moduleStructure
      (body element addressWidth readCount) layerChildren)
      (cycleContract element addressWidth readCount)
      (stateCorresponds element addressWidth readCount layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches : ∀ index : Fin (entryCount addressWidth),
      (childContracts element addressWidth readCount (storage index)).EvaluatesTo
        (ProposedValues.childInputs (body element addressWidth readCount)
          (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (storage index))
        (fun | .stored => contractState .entries index)
        (proposal.2 (storage index)).outputs
        ((childContracts element addressWidth readCount (storage index)).stateRule.apply
          (ProposedValues.childInputs (body element addressWidth readCount)
            (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index)) ∧
      (layerChildren (storage index)).certification.stateCorresponds
        ((childContracts element addressWidth readCount (storage index)).stateRule.apply
          (ProposedValues.childInputs (body element addressWidth readCount)
            (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index))
        (proposal.2 (storage index)).nextState := by
    intro index
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
      inputs structuralState proposal satisfies (storage index)
      (fun | .stored => contractState .entries index) (corresponds index)
  have storageCurrent : ∀ index : Fin (entryCount addressWidth),
      (proposal.2 (storage index)).outputs .q = contractState .entries index := by
    intro index
    exact (EnabledRegister.observeRule_holds_iff element _ _ _).mp
      ((storageMatches index).1.1 EnabledRegister.Rule.observe)

  rcases (layerChildren decoder).certification.hasCorrespondingState
      (structuralState decoder) with ⟨decoderState, decoderCorresponds⟩
  have decoderState_eq : decoderState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst decoderState
  have decoderMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies decoder
    SignalMap.emptyValues decoderCorresponds
  have decoderValue (index : Fin (entryCount addressWidth)) :
      (proposal.2 decoder).outputs .result index =
        BinaryToOneHot.oneHot addressWidth (inputs .writeAddress) index := by
    have held := decoderMatches.1.1 BinaryToOneHot.Rule.apply
    have result := BinaryToOneHot.result_of_holds addressWidth _ _ _ held index
    rw [show (ProposedValues.childInputs (body element addressWidth readCount)
        (fun child => (layerChildren child).moduleStructure) inputs proposal.2 decoder) .value =
        inputs .writeAddress by rfl] at result
    exact result

  rcases (layerChildren decodeSplit).certification.hasCorrespondingState
      (structuralState decodeSplit) with ⟨splitState, splitCorresponds⟩
  have splitState_eq : splitState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst splitState
  have splitMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies decodeSplit
    SignalMap.emptyValues splitCorresponds
  have splitValue (index : Fin (entryCount addressWidth)) :
      (proposal.2 decodeSplit).outputs index = (proposal.2 decoder).outputs .result index := by
    have equal := (Composition.SignalSplitter.outputRule_holds_iff
      (Composition.SignalSplitter.vector (entryCount addressWidth) .bit) _ _ _).mp
      (splitMatches.1.1 Composition.SignalComponentRule.apply)
    exact congrFun equal index

  have gateValue (index : Fin (entryCount addressWidth)) :
      (proposal.2 (gate index)).outputs .output =
        (BinaryToOneHot.oneHot addressWidth (inputs .writeAddress) index &&
          inputs .writeEnable) := by
    have gateStateSubsingleton :
        Subsingleton (childContracts element addressWidth readCount (gate index)).state.Values := by
      change Subsingleton emptySignalMap.Values
      infer_instance
    have gateMatches :=
      letI := gateStateSubsingleton
      Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies (gate index)
        SignalMap.emptyValues
    have held := gateMatches.1.1 Primitives.AndRule.apply
    change Primitives.andOutputRule.Holds _ SignalMap.emptyValues _ at held
    rw [Primitives.andOutputRule_holds_iff] at held
    rw [show (ProposedValues.childInputs (body element addressWidth readCount)
          (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (gate index)) .left =
          inputs .writeEnable by rfl,
      show (ProposedValues.childInputs (body element addressWidth readCount)
          (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (gate index)) .right =
          (proposal.2 decodeSplit).outputs index by rfl,
      splitValue index, decoderValue index] at held
    simpa [Bool.and_comm] using held

  rcases (layerChildren combine).certification.hasCorrespondingState
      (structuralState combine) with ⟨combineState, combineCorresponds⟩
  have combineState_eq : combineState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst combineState
  have combineMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies combine
    SignalMap.emptyValues combineCorresponds
  have combineValue : (proposal.2 combine).outputs .value =
      fun index => (proposal.2 (storage index)).outputs .q := by
    have equal := (Composition.SignalCombiner.outputRule_holds_iff
      (entryCombiner element addressWidth) _ _ _).mp
      (combineMatches.1.1 Composition.SignalComponentRule.apply)
    exact congrFun equal Composition.AggregatePort.value

  have muxValue (port : Fin readCount) : (proposal.2 (readMux port)).outputs .result =
      contractState .entries
        (BitVector.toIndex addressWidth (inputs (.readAddress port))) := by
    rcases (layerChildren (readMux port)).certification.hasCorrespondingState
        (structuralState (readMux port)) with ⟨muxState, muxCorresponds⟩
    have muxState_eq : muxState = SignalMap.emptyValues := by
      funext statePort; exact nomatch statePort
    subst muxState
    have muxMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
      layerChildren inputs structuralState proposal satisfies
      (readMux port) SignalMap.emptyValues muxCorresponds
    have held := muxMatches.1.1 CombMuxTree.Rule.apply
    change (CombMuxTree.outputRule element addressWidth).Holds
      (ProposedValues.childInputs (body element addressWidth readCount)
        (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (readMux port))
      SignalMap.emptyValues (proposal.2 (readMux port)).outputs at held
    rw [CombMuxTree.outputRule_holds_iff] at held
    rw [show (ProposedValues.childInputs (body element addressWidth readCount)
          (fun child => (layerChildren child).moduleStructure) inputs proposal.2
            (readMux port)) .values =
          (proposal.2 combine).outputs .value by rfl,
      show (ProposedValues.childInputs (body element addressWidth readCount)
          (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (readMux port)) .index =
          inputs (.readAddress port) by rfl] at held
    rw [held]
    unfold CombMuxTree.select
    change (proposal.2 combine).outputs .value
      (BitVector.toIndex addressWidth (inputs (.readAddress port))) = _
    rw [combineValue]
    change (proposal.2 (storage (BitVector.toIndex addressWidth
      (inputs (.readAddress port))))).outputs .q = _
    exact storageCurrent _

  let nextContractState : (stateMap element addressWidth).Values := fun
    | .entries => nextEntries addressWidth (inputs .writeEnable)
        (inputs .writeAddress) (inputs .writeValue) (contractState .entries)
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | read port =>
        rw [readRule_holds_iff]
        exact (satisfies.1 (.readValue port)).trans (muxValue port)
    · rfl
  · intro index
    have nextCorresponds := (storageMatches index).2
    change (layerChildren (storage index)).certification.stateCorresponds
      (fun | .stored => (nextContractState .entries) index)
      (proposal.2 (storage index)).nextState
    have nextStateEq : (fun | .stored => (nextContractState .entries) index) =
        (childContracts element addressWidth readCount (storage index)).stateRule.apply
          (ProposedValues.childInputs (body element addressWidth readCount)
            (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index) := by
      funext statePort
      cases statePort
      simp only [Contracts.Cycle.CycleStateRule.apply]
      change (if inputs .writeEnable && decide (index = BitVector.toIndex addressWidth
          (inputs .writeAddress)) then inputs .writeValue else contractState .entries index) =
        bif (proposal.2 (gate index)).outputs .output then inputs .writeValue
          else contractState .entries index
      rw [gateValue]
      rw [BinaryToOneHot.oneHot_eq_decode]
      by_cases equal : index = BitVector.toIndex addressWidth (inputs .writeAddress)
      · subst index
        simp [BinaryToOneHot.decode_eq_true_iff, Bool.and_comm]
      · have decodedFalse : BinaryToOneHot.decode addressWidth
            (inputs .writeAddress) index = false := by
          cases value : BinaryToOneHot.decode addressWidth (inputs .writeAddress) index
          · rfl
          · exact False.elim (equal ((BinaryToOneHot.decode_eq_true_iff _ _ _).mp value))
        simp [equal, decodedFalse]
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
