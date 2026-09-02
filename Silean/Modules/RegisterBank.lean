import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.BinaryToOneHot
import Silean.Modules.CombMuxTree
import Silean.Modules.EnabledRegister
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.And
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Modules.RegisterBank

open Silean
open Contracts.Cycle.Certification.Layer

/-- A synchronous-write bank containing `2 ^ addressWidth` entries of `element`,
with an independently addressed combinational output for each read port. -/
abbrev entryCount (addressWidth : Nat) := BinaryToOneHot.size addressWidth

inductive Input (readCount : Nat)
  | writeEnable
  | writeAddress
  | writeValue
  | readAddress (port : Fin readCount)

instance (readCount : Nat) : Enumeration (Input readCount) :=
  let reads := (Enumeration.fin readCount).values.map Input.readAddress
  { values := [.writeEnable, .writeAddress, .writeValue] ++ reads
    nodup := by
      apply List.nodup_append.mpr
      refine ⟨by simp, List.nodup_map_of_injective Input.readAddress
        (by intro left right equal; injection equal) (Enumeration.fin readCount).nodup, ?_⟩
      intro fixed fixedMem read readMem equal
      rcases List.mem_map.mp readMem with ⟨port, _, rfl⟩
      simp at fixedMem
      rcases fixedMem with rfl | rfl | rfl <;> cases equal
    locate
      | .writeEnable => .head
      | .writeAddress => .tail .head
      | .writeValue => .tail (.tail .head)
      | .readAddress port =>
          ListIndex.prependMany [.writeEnable, .writeAddress, .writeValue]
            (((Enumeration.fin _).locate port).map Input.readAddress) }

inductive Output (readCount : Nat)
  | readValue (port : Fin readCount)

@[reducible] def outputEnumeration (readCount : Nat) : Enumeration (Output readCount) :=
  let ports := Enumeration.fin readCount
  { values := ports.values.map Output.readValue
    nodup := List.nodup_map_of_injective Output.readValue
      (by intro left right equal; injection equal) ports.nodup
    locate := fun | .readValue port => (ports.locate port).map Output.readValue }

instance (readCount : Nat) : Enumeration (Output readCount) := outputEnumeration readCount

@[reducible] def inputMap (element : SignalType) (addressWidth readCount : Nat) : SignalMap :=
  EnumeratedMap.of (Input readCount) fun
    | .writeEnable => .bit
    | .writeAddress | .readAddress _ => .vector addressWidth .bit
    | .writeValue => element

@[reducible] def outputMap (element : SignalType) (readCount : Nat) : SignalMap :=
  { Key := Output readCount
    keys := outputEnumeration readCount
    value := fun | .readValue _ => element }

@[reducible] def ports (element : SignalType) (addressWidth readCount : Nat) : ModulePorts :=
  ⟨inputMap element addressWidth readCount, outputMap element readCount⟩

inductive State
  /-- The value currently held in every bank entry. -/
  | entries
deriving Enumeration

@[reducible] def stateMap (element : SignalType) (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of State fun
    | .entries => .vector (entryCount addressWidth) element

inductive Rule (readCount : Nat)
  | read (port : Fin readCount)

@[reducible] def ruleEnumeration (readCount : Nat) : Enumeration (Rule readCount) :=
  let ports := Enumeration.fin readCount
  { values := ports.values.map Rule.read
    nodup := List.nodup_map_of_injective Rule.read
      (by intro left right equal; injection equal) ports.nodup
    locate := fun | .read port => (ports.locate port).map Rule.read }

instance (readCount : Nat) : Enumeration (Rule readCount) := ruleEnumeration readCount

def nextEntries (addressWidth : Nat) (writeEnable : Bool)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (entryCount addressWidth) → α) :
    Fin (entryCount addressWidth) → α :=
  fun index =>
    if writeEnable && decide (index = BitVector.toIndex addressWidth writeAddress)
    then writeValue
    else entries index

def readRule (element : SignalType) (addressWidth readCount : Nat) (port : Fin readCount) :
    Contracts.Cycle.CycleOutputRule (ports element addressWidth readCount) (stateMap element addressWidth)
      { inputTypes := .cons (.vector addressWidth .bit) .nil
        outputTypes := .cons element .nil } where
  readsInputs := (inputMap element addressWidth readCount).select (.readAddress port)
  writesOutputs := (outputMap element readCount).select (.readValue port)
  target
    | (readAddress, ()), state =>
        (state .entries (BitVector.toIndex addressWidth readAddress), ())

def stateRule (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.CycleStateRule (ports element addressWidth readCount) (stateMap element addressWidth) where
  inputTypes := .cons .bit
    (.cons (.vector addressWidth .bit) (.cons element .nil))
  readsInputs := (((inputMap element addressWidth readCount).select .writeValue).prepend
    .writeAddress).prepend .writeEnable
  target
    | (writeEnable, (writeAddress, (writeValue, ()))), state => fun
        | .entries => nextEntries addressWidth writeEnable writeAddress writeValue
            (state .entries)

@[reducible] def cycleContract (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element addressWidth readCount) where
  state := stateMap element addressWidth
  RuleName := Rule readCount
  ruleNames := ruleEnumeration readCount
  outputRule | .read port => ⟨_, readRule element addressWidth readCount port⟩
  stateRule := stateRule element addressWidth readCount
  outputCoverage := by
    simp only [readRule, outputMap, SignalMap.select, SignalSelection.labels,
      outputEnumeration]
    change (List.flatMap (fun name : Rule readCount => [Output.readValue name.1])
      (ruleEnumeration readCount).values).Perm (outputEnumeration readCount).values
    apply List.Perm.of_eq
    change (List.flatMap (fun name : Rule readCount => [Output.readValue name.1])
      ((Enumeration.fin readCount).values.map Rule.read)) =
      ((Enumeration.fin readCount).values.map Output.readValue)
    induction (Enumeration.fin readCount).values with
    | nil => rfl
    | cons head tail induction => simp [induction]

@[simp] theorem readRule_holds_iff (element : SignalType) (addressWidth readCount : Nat)
    (port : Fin readCount)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth readCount).outputs.Values) :
    (readRule element addressWidth readCount port).Holds inputs state outputs ↔
      outputs (.readValue port) =
        state .entries (BitVector.toIndex addressWidth (inputs (.readAddress port))) := by
  simp [readRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem nextEntries_selected (addressWidth : Nat)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (entryCount addressWidth) → α) :
    nextEntries addressWidth true writeAddress writeValue entries
      (BitVector.toIndex addressWidth writeAddress) = writeValue := by
  simp [nextEntries]

@[simp] theorem nextEntries_disabled (addressWidth : Nat)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (entryCount addressWidth) → α) :
    nextEntries addressWidth false writeAddress writeValue entries = entries := by
  funext index
  simp [nextEntries]

theorem nextEntries_other (addressWidth : Nat) (writeEnable : Bool)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (entryCount addressWidth) → α)
    (index : Fin (entryCount addressWidth))
    (different : index ≠ BitVector.toIndex addressWidth writeAddress) :
    nextEntries addressWidth writeEnable writeAddress writeValue entries index =
      entries index := by
  simp [nextEntries, different]

/-! ## Hardware structure -/

private inductive Instance (addressWidth readCount : Nat)
  /-- Decodes the binary write address into one-hot form. -/
  | decoder
  /-- Exposes the individual one-hot write-select bits. -/
  | decodeSplit
  /-- Combines global write enable with one entry's select bit. -/
  | gate (index : Fin (entryCount addressWidth))
  /-- Stores one data entry. -/
  | storage (index : Fin (entryCount addressWidth))
  /-- Collects all stored entries into a vector. -/
  | combine
  /-- Selects the asynchronously read entry. -/
  | readMux (port : Fin readCount)

@[reducible] private def instanceEnumeration (addressWidth readCount : Nat) :
    Enumeration (Instance addressWidth readCount) :=
  let indices := Enumeration.fin (entryCount addressWidth)
  let gates := indices.values.map Instance.gate
  let stores := indices.values.map Instance.storage
  let readMuxes := (Enumeration.fin readCount).values.map Instance.readMux
  {
    values := [Instance.decoder, Instance.decodeSplit] ++ gates ++ stores ++
      [Instance.combine] ++ readMuxes
    nodup := by
      have gatesNodup : gates.Nodup :=
        List.nodup_map_of_injective Instance.gate
          (by intro left right equal; exact Instance.gate.inj equal) indices.nodup
      have storesNodup : stores.Nodup :=
        List.nodup_map_of_injective Instance.storage
          (by intro left right equal; exact Instance.storage.inj equal) indices.nodup
      have prefixGates :
          ([Instance.decoder, Instance.decodeSplit] ++ gates).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨by simp, gatesNodup, ?_⟩
        intro fixed fixedMem mapped mappedMem equal
        rcases List.mem_map.mp mappedMem with ⟨index, _, rfl⟩
        simp at fixedMem
        rcases fixedMem with rfl | rfl <;> cases equal
      have prefixStores :
          ([Instance.decoder, Instance.decodeSplit] ++ gates ++ stores).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨prefixGates, storesNodup, ?_⟩
        intro old oldMem mapped mappedMem equal
        rcases List.mem_map.mp mappedMem with ⟨index, _, rfl⟩
        cases equal
        simp [gates] at oldMem
      have prefixCombine :
          ([Instance.decoder, Instance.decodeSplit] ++ gates ++ stores ++
            [Instance.combine]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨prefixStores, by simp, ?_⟩
        intro old oldMem combined combinedMem equal
        simp at combinedMem
        subst combined
        subst old
        simp [gates, stores] at oldMem
      have muxesNodup : readMuxes.Nodup :=
        List.nodup_map_of_injective Instance.readMux
          (by intro left right equal; exact Instance.readMux.inj equal)
          (Enumeration.fin readCount).nodup
      apply List.nodup_append.mpr
      refine ⟨prefixCombine, muxesNodup, ?_⟩
      intro old oldMem mapped mappedMem equal
      rcases List.mem_map.mp mappedMem with ⟨port, _, rfl⟩
      cases equal
      simp [gates, stores] at oldMem
    locate
      | .decoder => .head
      | .decodeSplit => .tail .head
      | .gate index => by
          simpa only [gates, List.append_assoc] using
            ListIndex.prependMany [.decoder, .decodeSplit]
              (((Enumeration.fin _).locate index).map Instance.gate |>.appendRight
                (stores ++ ([.combine] ++ readMuxes)))
      | .storage index =>
          by
            simp only [List.append_assoc]
            exact ListIndex.prependMany [.decoder, .decodeSplit]
              (ListIndex.prependMany gates
                (((Enumeration.fin _).locate index).map Instance.storage |>.appendRight
                  ([.combine] ++ readMuxes)))
      | .combine =>
          by
            simpa only [List.append_assoc, List.singleton_append] using
              ListIndex.prependMany [.decoder, .decodeSplit]
                (ListIndex.prependMany gates
                  (ListIndex.prependMany stores
                    (show ListIndex Instance.combine
                      (Instance.combine :: readMuxes) from .head)))
      | .readMux port =>
          ListIndex.prependMany ([.decoder, .decodeSplit] ++ gates ++ stores ++ [.combine])
            (((Enumeration.fin _).locate port).map Instance.readMux)
  }

private abbrev decoder : Instance addressWidth readCount := .decoder
private abbrev decodeSplit : Instance addressWidth readCount := .decodeSplit
private abbrev gate (index : Fin (entryCount addressWidth)) : Instance addressWidth readCount := .gate index
private abbrev storage (index : Fin (entryCount addressWidth)) : Instance addressWidth readCount := .storage index
private abbrev combine : Instance addressWidth readCount := .combine
private abbrev readMux (port : Fin readCount) : Instance addressWidth readCount := .readMux port

private def entryCombiner (element : SignalType) (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector (entryCount addressWidth) element

@[reducible] private def instancePorts (element : SignalType) (addressWidth readCount : Nat) : InstancePorts where
  Key := Instance addressWidth readCount
  keys := instanceEnumeration addressWidth readCount
  value
    | .decoder => BinaryToOneHot.ports addressWidth
    | .decodeSplit => (Composition.SignalSplitter.vector (entryCount addressWidth) .bit).ports
    | .gate _ => Primitives.and.ports
    | .storage _ => EnabledRegister.ports element
    | .combine => (entryCombiner element addressWidth).ports
    | .readMux _ => CombMuxTree.ports element addressWidth

@[reducible] private def context (element : SignalType) (addressWidth readCount : Nat) : EndpointContext where
  ports := ports element addressWidth readCount
  instancePorts := instancePorts element addressWidth readCount

private def wiring (element : SignalType) (addressWidth readCount : Nat) :
    Wiring (context element addressWidth readCount).ports
      (context element addressWidth readCount).instancePorts :=
  let c := context element addressWidth readCount
  { moduleOutput := fun
    -- Each read mux directly drives its corresponding bank output.
    | .readValue port => c.instanceOutput (.readMux port) .result
    instanceInput := fun
    -- Decode the write address and expose each one-hot bit.
    | .decoder, .value => c.moduleInput .writeAddress
    | .decodeSplit, .value =>
        c.instanceOutput .decoder .result
    -- Enable only the addressed entry when a write is requested.
    | .gate _, .left =>
        c.moduleInput .writeEnable
    | .gate index, .right =>
        c.instanceOutput .decodeSplit index
    -- Every entry sees the write value; its local gate controls loading.
    | .storage _, .value =>
        c.moduleInput .writeValue
    | .storage index, .enable =>
        c.instanceOutput (.gate index) .output
    -- Collect the entries and select one using the read address.
    | .combine, index =>
        c.instanceOutput (.storage index) .value
    | .readMux _, .values =>
        c.instanceOutput .combine .value
    | .readMux port, .index =>
        c.moduleInput (.readAddress port) }

@[reducible] private def body (element : SignalType) (addressWidth readCount : Nat) : ModuleBody :=
  ⟨context element addressWidth readCount, wiring element addressWidth readCount⟩

@[reducible] private def structuralChildren (element : SignalType) (addressWidth readCount : Nat) :
    (name : (instancePorts element addressWidth readCount).Name) →
      ModuleStructure ((instancePorts element addressWidth readCount).ports name)
  | .decoder => BinaryToOneHot.moduleStructure addressWidth
  | .decodeSplit => (Composition.SignalSplitter.vector (entryCount addressWidth) .bit).certified.moduleStructure
  | .gate _ => Primitives.andCertified.moduleStructure
  | .storage _ => EnabledRegister.moduleStructure element
  | .combine => (entryCombiner element addressWidth).certified.moduleStructure
  | .readMux _ => CombMuxTree.moduleStructure element addressWidth

def moduleStructure (element : SignalType) (addressWidth readCount : Nat) :
    ModuleStructure (ports element addressWidth readCount) :=
  .composite (body element addressWidth readCount) (structuralChildren element addressWidth readCount)

/-- The register bank and every module below it have concrete structure. Callers
can use this fact without unfolding the bank's private instances or wiring. -/
@[reducible] private def childContracts (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.ChildCycleContracts (body element addressWidth readCount)
  | .decoder => BinaryToOneHot.cycleContract addressWidth
  | .decodeSplit =>
      (Composition.SignalSplitter.vector (entryCount addressWidth) .bit).cycleContract
  | .gate _ => Primitives.andCycleContract
  | .storage _ => EnabledRegister.cycleContract element
  | .combine => (entryCombiner element addressWidth).cycleContract
  | .readMux _ => CombMuxTree.cycleContract element addressWidth

private abbrev decoderOccurrence (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.decoder, BinaryToOneHot.Rule.apply⟩

private abbrev splitOccurrence (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.decodeSplit, Composition.SignalComponentRule.apply⟩

private abbrev gateOccurrence (element : SignalType) (addressWidth readCount : Nat)
    (index : Fin (entryCount addressWidth)) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.gate index, Primitives.AndRule.apply⟩

private abbrev storageOccurrence (element : SignalType) (addressWidth readCount : Nat)
    (index : Fin (entryCount addressWidth)) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.storage index, EnabledRegister.Rule.observe⟩

private abbrev combineOccurrence (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.combine, Composition.SignalComponentRule.apply⟩

private abbrev muxOccurrence (element : SignalType) (addressWidth readCount : Nat)
    (port : Fin readCount) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element addressWidth readCount) (childContracts element addressWidth readCount) :=
  ⟨.readMux port, CombMuxTree.Rule.apply⟩



private def scheduleOrders (element : SignalType)
    (addressWidth readCount : Nat) :
    ScheduleDerivation.RuleScheduleOrders (body element addressWidth readCount)
      (childContracts element addressWidth readCount)
      (cycleContract element addressWidth readCount) where
  output := fun
    | .read port => (Enumeration.fin (entryCount addressWidth)).values.map
        (storageOccurrence element addressWidth readCount) ++
      [combineOccurrence element addressWidth readCount,
        muxOccurrence element addressWidth readCount port]
  state := [decoderOccurrence element addressWidth readCount,
      splitOccurrence element addressWidth readCount] ++
    (Enumeration.fin (entryCount addressWidth)).values.map
      (gateOccurrence element addressWidth readCount) ++
    (Enumeration.fin (entryCount addressWidth)).values.map
      (storageOccurrence element addressWidth readCount) ++
    [combineOccurrence element addressWidth readCount]

private noncomputable def derivedRuleSchedules (element : SignalType)
    (addressWidth readCount : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (body element addressWidth readCount)
      (childContracts element addressWidth readCount)
      (cycleContract element addressWidth readCount) := by
  derive_rule_schedules (scheduleOrders element addressWidth readCount)

private noncomputable def ruleSchedules (element : SignalType) (addressWidth readCount : Nat) :=
  (derivedRuleSchedules element addressWidth readCount).schedules

private theorem coversChildren (element : SignalType) (addressWidth readCount : Nat) :
    (ruleSchedules element addressWidth readCount).CoversChildren :=
  (derivedRuleSchedules element addressWidth readCount).coversChildren

section LayerCertification

variable (element : SignalType) (addressWidth readCount : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body element addressWidth readCount) (childContracts element addressWidth readCount))

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
      (proposal.2 (storage index)).outputs .value = contractState .entries index := by
    intro index
    exact (EnabledRegister.outputRule_holds_iff element _ _ _).mp
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
      fun index => (proposal.2 (storage index)).outputs .value := by
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
      (inputs (.readAddress port))))).outputs .value = _
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
      (fun | .stored => nextContractState .entries index)
      (proposal.2 (storage index)).nextState
    rw [show (fun | .stored => nextContractState .entries index) =
        (childContracts element addressWidth readCount (storage index)).stateRule.apply
          (ProposedValues.childInputs (body element addressWidth readCount)
            (fun child => (layerChildren child).moduleStructure) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index) by
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
        simp [equal, decodedFalse]]
    exact nextCorresponds

end LayerCertification

/-- The register-bank wiring implements its cycle contract using only the
public contracts of its decoder, storage, and selection children. -/
noncomputable opaque certifiedLayer (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body element addressWidth readCount) (childContracts element addressWidth readCount)
      (cycleContract element addressWidth readCount) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules element addressWidth readCount)
    (coversChildren element addressWidth readCount)
    (stateCorresponds element addressWidth readCount)
    (hasCorrespondingState element addressWidth readCount)
    (implements element addressWidth readCount)

@[reducible] private noncomputable def certifiedChildren
    (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body element addressWidth readCount) (childContracts element addressWidth readCount)
  | .decoder => (BinaryToOneHot.certified addressWidth).certifiedStructure
  | .decodeSplit =>
      (Composition.SignalSplitter.vector (entryCount addressWidth) .bit).certified.certifiedStructure
  | .gate _ => Primitives.andCertified.certifiedStructure
  | .storage _ => (EnabledRegister.certified element).certifiedStructure
  | .combine => (entryCombiner element addressWidth).certified.certifiedStructure
  | .readMux _ => (CombMuxTree.certified element addressWidth).certifiedStructure

noncomputable opaque certification (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure element addressWidth readCount)
      (cycleContract element addressWidth readCount) :=
  (certifiedLayer element addressWidth readCount).certifyComposite
    (structuralChildren element addressWidth readCount)
    (certifiedChildren element addressWidth readCount) (by
      intro child
      cases child <;> rfl)

noncomputable def certified (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports element addressWidth readCount) :=
  (certification element addressWidth readCount).bundle

@[simp] theorem certified_moduleStructure (element : SignalType) (addressWidth readCount : Nat) :
    (certified element addressWidth readCount).moduleStructure =
      moduleStructure element addressWidth readCount := rfl

@[simp] theorem certified_cycleContract (element : SignalType) (addressWidth readCount : Nat) :
    (certified element addressWidth readCount).cycleContract =
      cycleContract element addressWidth readCount := rfl

theorem hasExactlyOneSolution (element : SignalType) (addressWidth readCount : Nat)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (currentState : (moduleStructure element addressWidth readCount).State) :
    ∃ proposal,
      (moduleStructure element addressWidth readCount).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure element addressWidth readCount).IsSolution
        inputs currentState other → other = proposal :=
  (certified element addressWidth readCount).hasExactlyOneStructuralResult inputs currentState

@[simp] theorem stateRule_apply_entries (element : SignalType) (addressWidth readCount : Nat)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth readCount).apply inputs state .entries =
      nextEntries addressWidth (inputs .writeEnable) (inputs .writeAddress)
        (inputs .writeValue) (state .entries) := by
  rfl

theorem readValue_of_evaluatesTo (element : SignalType) (addressWidth readCount : Nat)
    (port : Fin readCount)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth readCount).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth readCount).EvaluatesTo
      inputs state outputs nextState) :
    outputs (.readValue port) =
      state .entries (BitVector.toIndex addressWidth (inputs (.readAddress port))) :=
  (readRule_holds_iff element addressWidth readCount port inputs state outputs).mp
    (evaluates.1 (.read port))

theorem written_entry_of_evaluatesTo (element : SignalType) (addressWidth readCount : Nat)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth readCount).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth readCount).EvaluatesTo
      inputs state outputs nextState)
    (enabled : inputs .writeEnable = true) :
    nextState .entries (BitVector.toIndex addressWidth (inputs .writeAddress)) =
      inputs .writeValue := by
  rw [evaluates.2, stateRule_apply_entries, enabled]
  exact nextEntries_selected _ _ _ _

theorem retained_entry_of_evaluatesTo (element : SignalType) (addressWidth readCount : Nat)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth readCount).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth readCount).EvaluatesTo
      inputs state outputs nextState)
    (index : Fin (entryCount addressWidth))
    (different : index ≠ BitVector.toIndex addressWidth (inputs .writeAddress)) :
    nextState .entries index = state .entries index := by
  rw [evaluates.2, stateRule_apply_entries]
  exact nextEntries_other _ _ _ _ _ _ different

end Silean.Modules.RegisterBank

namespace Silean.Modules.RegisterBank.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (addressWidth readCount : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.RegisterBank.ports element addressWidth readCount) where
  inputs := ⟨fun
    | .writeEnable => "write_enable"
    | .writeAddress => "write_address"
    | .writeValue => "write_value"
    | .readAddress port => s!"read_{port.val}_address"⟩
  outputs := ⟨fun | .readValue port => s!"read_{port.val}_value"⟩
  inputTypes := fun
    | .writeEnable => .bit
    | .writeAddress | .readAddress _ => .vector .bit
    | .writeValue => elementNaming
  outputTypes := fun | .readValue _ => elementNaming

def ports (element : SignalType) (addressWidth readCount : Nat) :
    ModulePortsNaming (Modules.RegisterBank.ports element addressWidth readCount) :=
  portsWithNaming element addressWidth readCount (.positional element)

def namingWith (element : SignalType) (addressWidth readCount : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth readCount) := by
  unfold Modules.RegisterBank.moduleStructure
  exact .composite ⟨"register_bank", "structural",
      [.shape element, .natural addressWidth, .natural readCount]⟩
    (portsWithNaming element addressWidth readCount elementNaming)
    (fun
      | .decoder => "write_decoder"
      | .decodeSplit => "write_decoder_split"
      | .gate index => s!"write_gate_{index.val}"
      | .storage index => s!"entry_{index.val}"
      | .combine => "entries"
      | .readMux port => s!"read_{port.val}_mux")
    (fun
      | .decoder => BinaryToOneHot.Naming.naming addressWidth
      | .decodeSplit => Silean.Naming.SignalAdapter.splitter
          (.vector (Modules.RegisterBank.entryCount addressWidth) .bit)
      | .gate _ => Silean.Naming.Primitive.and
      | .storage _ =>
          EnabledRegister.Naming.namingWith element elementNaming
      | .combine =>
          Silean.Naming.SignalAdapter.combinerWithNaming
            (Composition.SignalSplitter.vector
              (Modules.RegisterBank.entryCount addressWidth) element).combiner
            (.vector elementNaming)
      | .readMux _ =>
          CombMuxTree.Naming.namingWith element addressWidth elementNaming)

def naming (element : SignalType) (addressWidth readCount : Nat) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth readCount) :=
  namingWith element addressWidth readCount (.positional element)

end Silean.Modules.RegisterBank.Naming
