import Silean2.CertifiedSchedule
import Silean2.Modules.BinaryToOneHot
import Silean2.Modules.CombMuxTree
import Silean2.Modules.EnabledRegister
import Silean2.Naming.PrimitiveNaming
import Silean2.Naming.SignalAdapterNaming
import Silean2.Primitives.And
import Silean2.SignalAdapterCertified

namespace Silean2.Modules.RegisterBank

open Silean2

abbrev EntryCount (addressWidth : Nat) := BinaryToOneHot.size addressWidth

inductive Input
  | writeEnable
  | writeAddress
  | writeValue
  | readAddress
deriving Enumeration

inductive Output | readValue
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .writeEnable => .bit
    | .writeAddress | .readAddress => .vector addressWidth .bit
    | .writeValue => element

@[reducible] def outputMap (element : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .readValue => element

@[reducible] def ports (element : SignalType) (addressWidth : Nat) : ModulePorts :=
  ⟨inputMap element addressWidth, outputMap element⟩

inductive State | entries
deriving Enumeration

@[reducible] def stateMap (element : SignalType) (addressWidth : Nat) : SignalMap :=
  EnumeratedMap.of State fun
    | .entries => .vector (EntryCount addressWidth) element

inductive Rule | read
deriving Enumeration

def nextEntries (addressWidth : Nat) (writeEnable : Bool)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (EntryCount addressWidth) → α) :
    Fin (EntryCount addressWidth) → α :=
  fun index =>
    if writeEnable && decide (index = BitVector.toIndex addressWidth writeAddress)
    then writeValue
    else entries index

def readRule (element : SignalType) (addressWidth : Nat) :
    CycleOutputRule (ports element addressWidth) (stateMap element addressWidth)
      { inputTypes := .cons (.vector addressWidth .bit) .nil
        outputTypes := .cons element .nil } where
  readsInputs := (inputMap element addressWidth).select .readAddress
  writesOutputs := (outputMap element).select .readValue
  target
    | (readAddress, ()), state =>
        (state .entries (BitVector.toIndex addressWidth readAddress), ())

def stateRule (element : SignalType) (addressWidth : Nat) :
    CycleStateRule (ports element addressWidth) (stateMap element addressWidth) where
  inputTypes := .cons .bit
    (.cons (.vector addressWidth .bit) (.cons element .nil))
  readsInputs := (((inputMap element addressWidth).select .writeValue).prepend
    .writeAddress).prepend .writeEnable
  target
    | (writeEnable, (writeAddress, (writeValue, ()))), state => fun
        | .entries => nextEntries addressWidth writeEnable writeAddress writeValue
            (state .entries)

@[reducible] def cycleContract (element : SignalType) (addressWidth : Nat) :
    ModuleCycleContract (ports element addressWidth) where
  state := stateMap element addressWidth
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .read => ⟨_, readRule element addressWidth⟩
  stateRule := stateRule element addressWidth
  outputCoverage := by rfl

@[simp] theorem readRule_holds_iff (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth).outputs.Values) :
    (readRule element addressWidth).Holds inputs state outputs ↔
      outputs .readValue =
        state .entries (BitVector.toIndex addressWidth (inputs .readAddress)) := by
  simp [readRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem nextEntries_selected (addressWidth : Nat)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (EntryCount addressWidth) → α) :
    nextEntries addressWidth true writeAddress writeValue entries
      (BitVector.toIndex addressWidth writeAddress) = writeValue := by
  simp [nextEntries]

@[simp] theorem nextEntries_disabled (addressWidth : Nat)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (EntryCount addressWidth) → α) :
    nextEntries addressWidth false writeAddress writeValue entries = entries := by
  funext index
  simp [nextEntries]

theorem nextEntries_other (addressWidth : Nat) (writeEnable : Bool)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (EntryCount addressWidth) → α)
    (index : Fin (EntryCount addressWidth))
    (different : index ≠ BitVector.toIndex addressWidth writeAddress) :
    nextEntries addressWidth writeEnable writeAddress writeValue entries index =
      entries index := by
  simp [nextEntries, different]

/-! The implementation has one decoder, one write-enable gate and enabled
register per entry, one vector combiner, and one combinational read mux. -/

private inductive Instance (addressWidth : Nat)
  | decoder
  | decodeSplit
  | gate (index : Fin (EntryCount addressWidth))
  | storage (index : Fin (EntryCount addressWidth))
  | combine
  | readMux

@[reducible] private def instanceEnumeration (addressWidth : Nat) :
    Enumeration (Instance addressWidth) :=
  let indices := Enumeration.fin (EntryCount addressWidth)
  let gates := indices.values.map Instance.gate
  let stores := indices.values.map Instance.storage
  {
    values := [.decoder, .decodeSplit] ++ gates ++ stores ++ [.combine, .readMux]
    nodup := by
      have gatesNodup : gates.Nodup :=
        List.nodup_map_of_injective Instance.gate
          (by intro left right equal; exact Instance.gate.inj equal) indices.nodup
      have storesNodup : stores.Nodup :=
        List.nodup_map_of_injective Instance.storage
          (by intro left right equal; exact Instance.storage.inj equal) indices.nodup
      apply List.nodup_append.mpr
      refine ⟨?_, by simp, ?_⟩
      · apply List.nodup_append.mpr
        refine ⟨?_, storesNodup, ?_⟩
        · apply List.nodup_append.mpr
          refine ⟨by simp, gatesNodup, ?_⟩
          intro oldValue oldMem gateValue gateMem equal
          rcases List.mem_map.mp gateMem with ⟨index, _, rfl⟩
          simp at oldMem
          subst oldValue
          rcases oldMem with equal | equal <;> cases equal
        · intro oldValue oldMem storeValue storeMem equal
          rcases List.mem_map.mp storeMem with ⟨storeIndex, _, rfl⟩
          rcases List.mem_append.mp oldMem with prefixMem | gateMem
          · simp at prefixMem
            subst oldValue
            rcases prefixMem with equal | equal <;> cases equal
          · rcases List.mem_map.mp gateMem with ⟨gateIndex, _, rfl⟩
            cases equal
      · intro old oldMem suffix suffixMem equal
        simp at suffixMem
        rcases suffixMem with rfl | rfl
        · cases equal
          simp [gates, stores] at oldMem
        · cases equal
          simp [gates, stores] at oldMem
    locate
      | .decoder => .head
      | .decodeSplit => .tail .head
      | .gate index => by
          simpa only [gates, List.append_assoc] using
            ListIndex.prependMany [.decoder, .decodeSplit]
              (((Enumeration.fin _).locate index).map Instance.gate |>.appendRight
                (stores ++ [.combine, .readMux]))
      | .storage index =>
          by
            simp only [List.append_assoc]
            exact ListIndex.prependMany [.decoder, .decodeSplit]
              (ListIndex.prependMany gates
                (((Enumeration.fin _).locate index).map Instance.storage |>.appendRight
                  [.combine, .readMux]))
      | .combine =>
          ListIndex.prependMany ([.decoder, .decodeSplit] ++ gates ++ stores) .head
      | .readMux =>
          ListIndex.prependMany ([.decoder, .decodeSplit] ++ gates ++ stores) (.tail .head)
  }

private abbrev decoder : Instance addressWidth := .decoder
private abbrev decodeSplit : Instance addressWidth := .decodeSplit
private abbrev gate (index : Fin (EntryCount addressWidth)) : Instance addressWidth := .gate index
private abbrev storage (index : Fin (EntryCount addressWidth)) : Instance addressWidth := .storage index
private abbrev combine : Instance addressWidth := .combine
private abbrev readMux : Instance addressWidth := .readMux

private def entryCombiner (element : SignalType) (addressWidth : Nat) : SignalCombiner :=
  .vector (EntryCount addressWidth) element

@[reducible] private def instances (element : SignalType) (addressWidth : Nat) : Instances where
  Key := Instance addressWidth
  keys := instanceEnumeration addressWidth
  value
    | .decoder => BinaryToOneHot.ports addressWidth
    | .decodeSplit => (SignalSplitter.vector (EntryCount addressWidth) .bit).ports
    | .gate _ => Primitives.and.ports
    | .storage _ => EnabledRegister.ports element
    | .combine => (entryCombiner element addressWidth).ports
    | .readMux => CombMuxTree.ports element addressWidth

@[reducible] private def context (element : SignalType) (addressWidth : Nat) : EndpointContext where
  ports := ports element addressWidth
  instances := instances element addressWidth

private def wiring (element : SignalType) (addressWidth : Nat) :
    Wiring (context element addressWidth).ports (context element addressWidth).instances where
  moduleOutput
    | .readValue => (context element addressWidth).instanceOutput .readMux .result
  instanceInput
    | .decoder, .value => (context element addressWidth).moduleInput .writeAddress
    | .decodeSplit, .value =>
        (context element addressWidth).instanceOutput .decoder .result
    | .gate _, .left =>
        (context element addressWidth).moduleInput .writeEnable
    | .gate index, .right =>
        (context element addressWidth).instanceOutput .decodeSplit index
    | .storage _, .value =>
        (context element addressWidth).moduleInput .writeValue
    | .storage index, .enable =>
        (context element addressWidth).instanceOutput (.gate index) .output
    | .combine, index =>
        (context element addressWidth).instanceOutput (.storage index) .value
    | .readMux, .values =>
        (context element addressWidth).instanceOutput .combine .value
    | .readMux, .index =>
        (context element addressWidth).moduleInput .readAddress

@[reducible] private def body (element : SignalType) (addressWidth : Nat) : ModuleBody :=
  ⟨context element addressWidth, wiring element addressWidth⟩

@[reducible] private noncomputable def children (element : SignalType) (addressWidth : Nat) :
    Certified.Children (body element addressWidth)
  | .decoder => BinaryToOneHot.certified addressWidth
  | .decodeSplit => (SignalSplitter.vector (EntryCount addressWidth) .bit).certified
  | .gate _ => Primitives.andCertified
  | .storage _ => EnabledRegister.certified element
  | .combine => (entryCombiner element addressWidth).certified
  | .readMux => CombMuxTree.certified element addressWidth

@[reducible] private def structuralChildren (element : SignalType) (addressWidth : Nat) :
    (name : (instances element addressWidth).Name) →
      ModuleStructure ((instances element addressWidth).ports name)
  | .decoder => BinaryToOneHot.moduleStructure addressWidth
  | .decodeSplit => (SignalSplitter.vector (EntryCount addressWidth) .bit).certified.moduleStructure
  | .gate _ => Primitives.andCertified.moduleStructure
  | .storage _ => EnabledRegister.moduleStructure element
  | .combine => (entryCombiner element addressWidth).certified.moduleStructure
  | .readMux => CombMuxTree.moduleStructure element addressWidth

def moduleStructure (element : SignalType) (addressWidth : Nat) :
    ModuleStructure (ports element addressWidth) :=
  .composite (body element addressWidth) (structuralChildren element addressWidth)

private theorem moduleStructure_eq (element : SignalType) (addressWidth : Nat) :
    moduleStructure element addressWidth =
      Certified.moduleStructure (body element addressWidth)
        (children element addressWidth) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

@[reducible] private noncomputable def childStructure (element : SignalType) (addressWidth : Nat) :=
  Certified.childStructure (children element addressWidth)

private abbrev decoderOccurrence (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.decoder, BinaryToOneHot.Rule.apply⟩

private abbrev splitOccurrence (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.decodeSplit, SignalComponentRule.apply⟩

private abbrev gateOccurrence (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.gate index, Primitives.AndRule.apply⟩

private abbrev storageOccurrence (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.storage index, EnabledRegister.Rule.observe⟩

private abbrev combineOccurrence (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.combine, SignalComponentRule.apply⟩

private abbrev muxOccurrence (element : SignalType) (addressWidth : Nat) :
    Certified.RuleOccurrence (children element addressWidth) :=
  ⟨.readMux, CombMuxTree.Rule.apply⟩

@[simp] private theorem decoder_reads (element : SignalType) (addressWidth : Nat) :
    (decoderOccurrence element addressWidth).reads = [.value] := rfl
@[simp] private theorem decoder_writes (element : SignalType) (addressWidth : Nat) :
    (decoderOccurrence element addressWidth).writes = [.result] := rfl
@[simp] private theorem split_reads (element : SignalType) (addressWidth : Nat) :
    (splitOccurrence element addressWidth).reads = [.value] := rfl
@[simp] private theorem split_writes (element : SignalType) (addressWidth : Nat) :
    (splitOccurrence element addressWidth).writes =
      (Enumeration.fin (EntryCount addressWidth)).values := by
  change (SignalSplitter.vector (EntryCount addressWidth) .bit).ports.outputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]
@[simp] private theorem gate_reads (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    (gateOccurrence element addressWidth index).reads = [.left, .right] := rfl
@[simp] private theorem gate_writes (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    (gateOccurrence element addressWidth index).writes = [.output] := rfl
@[simp] private theorem storage_reads (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    (storageOccurrence element addressWidth index).reads = [] := rfl
@[simp] private theorem storage_writes (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    (storageOccurrence element addressWidth index).writes = [.value] := rfl
@[simp] private theorem combine_reads (element : SignalType) (addressWidth : Nat) :
    (combineOccurrence element addressWidth).reads =
      (Enumeration.fin (EntryCount addressWidth)).values := by
  change (entryCombiner element addressWidth).ports.inputs.allSelection.labels = _
  rw [SignalMap.allSelection_labels]
  rfl
@[simp] private theorem combine_writes (element : SignalType) (addressWidth : Nat) :
    (combineOccurrence element addressWidth).writes = [.value] := rfl
@[simp] private theorem mux_reads (element : SignalType) (addressWidth : Nat) :
    (muxOccurrence element addressWidth).reads = [.values, .index] := rfl
@[simp] private theorem mux_writes (element : SignalType) (addressWidth : Nat) :
    (muxOccurrence element addressWidth).writes = [.result] := rfl

private noncomputable def storageFamilySchedule (element : SignalType)
    (addressWidth : Nat) :
    Certified.Schedule (body element addressWidth) (children element addressWidth)
      (fun input => input ∈
        (readRule element addressWidth).readsInputs.labels)
      (fun final =>
        (∀ index, storageOccurrence element addressWidth index ∈ final) ∧
        ∀ called, called ∈ final →
          ∃ index, called = storageOccurrence element addressWidth index) [] :=
  Certified.Schedule.callFamily (Enumeration.fin (EntryCount addressWidth))
    (storageOccurrence element addressWidth)
    (by
      intro left right equal
      have childEqual := congrArg Certified.RuleOccurrence.child equal
      exact Instance.storage.inj childEqual)
    (by
      intro index input member
      change input ∈ ([] : List EnabledRegister.Input) at member
      cases member)

private noncomputable def outputSchedule (element : SignalType) (addressWidth : Nat) :
    Certified.OutputSchedule (body element addressWidth)
      (children element addressWidth) (cycleContract element addressWidth) .read := by
  let family := storageFamilySchedule element addressWidth
  apply family.append
  refine .call (combineOccurrence element addressWidth) ?_ ?_ ?_
  · intro index _
    exact ⟨EnabledRegister.Rule.observe, family.finished.1 index, by
      simp⟩
  · intro member
    rcases family.finished.2 _ member with ⟨index, equal⟩
    have childEqual := congrArg Certified.RuleOccurrence.child equal
    cases childEqual
  · refine .call (muxOccurrence element addressWidth) ?_ ?_ (.done ?_)
    · intro input _
      cases input with
      | values => exact ⟨SignalComponentRule.apply, by simp, by
          simp⟩
      | index =>
          change Input.readAddress ∈
            (readRule element addressWidth).readsInputs.labels
          simp [readRule, SignalMap.select, SignalSelection.labels]
    · intro member
      rcases List.mem_cons.mp member with equal | old
      · have childEqual := congrArg Certified.RuleOccurrence.child equal
        cases childEqual
      · rcases family.finished.2 _ old with ⟨index, equal⟩
        have childEqual := congrArg Certified.RuleOccurrence.child equal
        cases childEqual
    · intro output member
      cases output
      exact ⟨CombMuxTree.Rule.apply, by simp, by
        simp⟩

private noncomputable def gateFamilyAfterDecode (element : SignalType)
    (addressWidth : Nat) :
    Certified.Schedule (body element addressWidth) (children element addressWidth)
      (fun _ => True)
      (fun final =>
        (∀ called, called ∈
          [splitOccurrence element addressWidth, decoderOccurrence element addressWidth] →
            called ∈ final) ∧
        (∀ index, gateOccurrence element addressWidth index ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ [splitOccurrence element addressWidth,
            decoderOccurrence element addressWidth] ∨
          ∃ index, called = gateOccurrence element addressWidth index)
      [splitOccurrence element addressWidth, decoderOccurrence element addressWidth] :=
  Certified.Schedule.callFamilyAfter
    [splitOccurrence element addressWidth, decoderOccurrence element addressWidth]
    (Enumeration.fin (EntryCount addressWidth))
    (gateOccurrence element addressWidth)
    (by
      intro left right equal
      have childEqual := congrArg Certified.RuleOccurrence.child equal
      exact Instance.gate.inj childEqual)
    (by
      intro index member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal <;>
        have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
        cases childEqual)
    (by
      intro index input _
      cases input with
      | left => trivial
      | right => exact ⟨SignalComponentRule.apply, by simp, by
          simpa [split_writes] using
            (ListIndex.get_eq ((Enumeration.fin _).locate index) ▸ List.get_mem _ _)⟩
      )

private structure StateScheduleData (element : SignalType) (addressWidth : Nat) where
  schedule : Certified.StateSchedule (body element addressWidth)
    (children element addressWidth)
  decoderMem : decoderOccurrence element addressWidth ∈ schedule.finalAvailability
  splitMem : splitOccurrence element addressWidth ∈ schedule.finalAvailability
  gateMem : ∀ index, gateOccurrence element addressWidth index ∈ schedule.finalAvailability
  storageMem : ∀ index,
    storageOccurrence element addressWidth index ∈ schedule.finalAvailability

private noncomputable def makeStateSchedule (element : SignalType) (addressWidth : Nat) :
    StateScheduleData element addressWidth := by
  let gates := gateFamilyAfterDecode element addressWidth
  let stores := Certified.Schedule.callFamilyAfter
    (inputAvailable := fun _ => True) gates.finalAvailability
    (Enumeration.fin (EntryCount addressWidth))
    (storageOccurrence element addressWidth)
    (by
      intro left right equal
      have childEqual := congrArg Certified.RuleOccurrence.child equal
      exact Instance.storage.inj childEqual)
    (by
      intro index member
      rcases gates.finished.2.2 _ member with old | ⟨gateIndex, equal⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at old
        rcases old with equal | equal <;>
          have childEqual := congrArg Certified.RuleOccurrence.child equal <;>
          cases childEqual
      · have childEqual := congrArg Certified.RuleOccurrence.child equal
        cases childEqual)
    (by
      intro index input _
      cases input with
      | value => trivial
      | enable => exact ⟨Primitives.AndRule.apply, gates.finished.2.1 index, by simp⟩)
  let finish : Certified.ChildrenStateInputsReady (body element addressWidth)
      (children element addressWidth) stores.finalAvailability := by
      intro child input member
      cases child with
      | decoder =>
        change input ∈ ([] : List BinaryToOneHot.Input) at member
        cases member
      | decodeSplit =>
        change input ∈ ([] : List AggregatePort) at member
        cases member
      | gate index =>
        change input ∈ ([] : List Primitives.BinaryInput) at member
        cases member
      | storage index =>
        cases input with
        | value => trivial
        | enable =>
          exact ⟨Primitives.AndRule.apply,
            stores.finished.1 _ (gates.finished.2.1 index), by simp⟩
      | combine =>
        change input ∈ ([] : List (Fin (EntryCount addressWidth))) at member
        cases member
      | readMux =>
        change input ∈ ([] : List (CombMuxTree.Input)) at member
        cases member
  let tail : Certified.Schedule (body element addressWidth)
      (children element addressWidth) (fun _ => True)
      (Certified.ChildrenStateInputsReady (body element addressWidth)
        (children element addressWidth)) stores.finalAvailability :=
    .done finish
  let afterStores := stores.append tail
  let afterGates := gates.append afterStores
  let afterSplit : Certified.Schedule (body element addressWidth)
      (children element addressWidth) (fun _ => True)
      (Certified.ChildrenStateInputsReady (body element addressWidth)
        (children element addressWidth))
      [decoderOccurrence element addressWidth] :=
    .call (splitOccurrence element addressWidth)
      (by
        intro input _
        cases input
        exact ⟨BinaryToOneHot.Rule.apply, by simp, by simp⟩)
      (by simp) afterGates
  let schedule : Certified.StateSchedule (body element addressWidth)
      (children element addressWidth) :=
    .call (decoderOccurrence element addressWidth) (by intros; trivial)
      (by simp) afterSplit
  refine ⟨schedule, ?_, ?_, ?_, ?_⟩
  · dsimp [schedule, afterSplit]
    simp only [Certified.Schedule.finalAvailability]
    rw [Certified.Schedule.finalAvailability_append,
      Certified.Schedule.finalAvailability_append]
    exact stores.finished.1 _ (gates.finished.1 _ (by simp))
  · dsimp [schedule, afterSplit]
    simp only [Certified.Schedule.finalAvailability]
    rw [Certified.Schedule.finalAvailability_append,
      Certified.Schedule.finalAvailability_append]
    exact stores.finished.1 _ (gates.finished.1 _ (by simp))
  · intro index
    dsimp [schedule, afterSplit]
    simp only [Certified.Schedule.finalAvailability]
    rw [Certified.Schedule.finalAvailability_append,
      Certified.Schedule.finalAvailability_append]
    exact stores.finished.1 _ (gates.finished.2.1 index)
  · intro index
    dsimp [schedule, afterSplit]
    simp only [Certified.Schedule.finalAvailability]
    rw [Certified.Schedule.finalAvailability_append,
      Certified.Schedule.finalAvailability_append]
    exact stores.finished.2.1 index

private noncomputable def stateSchedule (element : SignalType) (addressWidth : Nat) :
    Certified.StateSchedule (body element addressWidth) (children element addressWidth) :=
  (makeStateSchedule element addressWidth).schedule

private noncomputable def ruleSchedules (element : SignalType) (addressWidth : Nat) :
    Certified.RuleSchedules (body element addressWidth)
      (children element addressWidth) (cycleContract element addressWidth) where
  output | .read => outputSchedule element addressWidth
  state := stateSchedule element addressWidth

private theorem output_mem_combine (element : SignalType) (addressWidth : Nat) :
    combineOccurrence element addressWidth ∈
      (outputSchedule element addressWidth).finalAvailability := by
  unfold outputSchedule
  rw [Certified.Schedule.finalAvailability_append]
  simp [Certified.Schedule.finalAvailability]

private theorem output_mem_mux (element : SignalType) (addressWidth : Nat) :
    muxOccurrence element addressWidth ∈
      (outputSchedule element addressWidth).finalAvailability := by
  unfold outputSchedule
  rw [Certified.Schedule.finalAvailability_append]
  simp [Certified.Schedule.finalAvailability]

private theorem state_mem_decoder (element : SignalType) (addressWidth : Nat) :
    decoderOccurrence element addressWidth ∈
      (stateSchedule element addressWidth).finalAvailability :=
  (makeStateSchedule element addressWidth).decoderMem

private theorem state_mem_split (element : SignalType) (addressWidth : Nat) :
    splitOccurrence element addressWidth ∈
      (stateSchedule element addressWidth).finalAvailability :=
  (makeStateSchedule element addressWidth).splitMem

private theorem state_mem_gate (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    gateOccurrence element addressWidth index ∈
      (stateSchedule element addressWidth).finalAvailability :=
  (makeStateSchedule element addressWidth).gateMem index

private theorem state_mem_storage (element : SignalType) (addressWidth : Nat)
    (index : Fin (EntryCount addressWidth)) :
    storageOccurrence element addressWidth index ∈
      (stateSchedule element addressWidth).finalAvailability :=
  (makeStateSchedule element addressWidth).storageMem index


private theorem coversChildren (element : SignalType) (addressWidth : Nat) :
    (ruleSchedules element addressWidth).CoversChildren := by
  intro child rule
  cases child with
  | decoder =>
    change BinaryToOneHot.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change decoderOccurrence element addressWidth ∈
      (stateSchedule element addressWidth).finalAvailability
    exact state_mem_decoder element addressWidth
  | decodeSplit =>
    change SignalComponentRule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change splitOccurrence element addressWidth ∈
      (stateSchedule element addressWidth).finalAvailability
    exact state_mem_split element addressWidth
  | gate index =>
    change Primitives.AndRule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change gateOccurrence element addressWidth index ∈
      (stateSchedule element addressWidth).finalAvailability
    exact state_mem_gate element addressWidth index
  | storage index =>
    change EnabledRegister.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change storageOccurrence element addressWidth index ∈
      (stateSchedule element addressWidth).finalAvailability
    exact state_mem_storage element addressWidth index
  | combine =>
    change SignalComponentRule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs
      (ruleSchedules element addressWidth) .read
    change combineOccurrence element addressWidth ∈
      (outputSchedule element addressWidth).finalAvailability
    exact output_mem_combine element addressWidth
  | readMux =>
    change CombMuxTree.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs
      (ruleSchedules element addressWidth) .read
    change muxOccurrence element addressWidth ∈
      (outputSchedule element addressWidth).finalAvailability
    exact output_mem_mux element addressWidth

private theorem hasAtMostOneSolution (element : SignalType) (addressWidth : Nat) :
    (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).HasAtMostOneSolution :=
  (ruleSchedules element addressWidth).hasAtMostOneSolution
    (coversChildren element addressWidth)

private def decoderInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values) :
    (BinaryToOneHot.ports addressWidth).inputs.Values
  | .value => inputs .writeAddress

private noncomputable def splitInputs (addressWidth : Nat)
    (decoderProposal : ProposedValues
      (children element addressWidth .decoder).moduleStructure) :
    (SignalSplitter.vector (EntryCount addressWidth) .bit).ports.inputs.Values
  | .value => decoderProposal.outputs .result

private noncomputable def gateInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (splitProposal : ProposedValues
      (children element addressWidth .decodeSplit).moduleStructure)
    (index : Fin (EntryCount addressWidth)) : Primitives.and.ports.inputs.Values
  | .left => inputs .writeEnable
  | .right => splitProposal.outputs index

private noncomputable def storageInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (gateProposals : ∀ index : Fin (EntryCount addressWidth),
      ProposedValues (children element addressWidth (.gate index)).moduleStructure)
    (index : Fin (EntryCount addressWidth)) :
    (EnabledRegister.ports element).inputs.Values
  | .value => inputs .writeValue
  | .enable => (gateProposals index).outputs .output

private noncomputable def combineInputs (element : SignalType) (addressWidth : Nat)
    (storageProposals : ∀ index : Fin (EntryCount addressWidth),
      ProposedValues (children element addressWidth (.storage index)).moduleStructure) :
    (entryCombiner element addressWidth).ports.inputs.Values :=
  fun index => (storageProposals index).outputs .value

private noncomputable def muxInputs (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (combineProposal : ProposedValues
      (children element addressWidth .combine).moduleStructure) :
    (CombMuxTree.ports element addressWidth).inputs.Values
  | .values => combineProposal.outputs .value
  | .index => inputs .readAddress

private theorem hasStructuralResult (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (currentState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) :
    ∃ proposal, (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).IsSolution inputs currentState proposal := by
  rcases (children element addressWidth .decoder).hasStructuralResult
      (decoderInputs element addressWidth inputs) (currentState .decoder) with
    ⟨decoderProposal, decoderSatisfies⟩
  rcases (children element addressWidth .decodeSplit).hasStructuralResult
      (splitInputs addressWidth decoderProposal) (currentState .decodeSplit) with
    ⟨splitProposal, splitSatisfies⟩
  let GateProperty := fun index proposal =>
    (children element addressWidth (.gate index)).moduleStructure.IsSolution
      (gateInputs element addressWidth inputs splitProposal index)
      (currentState (.gate index)) proposal
  have gatesAvailable : ∀ index, ∃ proposal, GateProperty index proposal := by
    intro index
    exact (children element addressWidth (.gate index)).hasStructuralResult
      (gateInputs element addressWidth inputs splitProposal index)
      (currentState (.gate index))
  rcases (Enumeration.fin (EntryCount addressWidth)).exists_pi
      GateProperty gatesAvailable with ⟨gateProposals, gateSatisfies⟩
  let StorageProperty := fun index proposal =>
    (children element addressWidth (.storage index)).moduleStructure.IsSolution
      (storageInputs element addressWidth inputs gateProposals index)
      (currentState (.storage index)) proposal
  have storesAvailable : ∀ index, ∃ proposal, StorageProperty index proposal := by
    intro index
    exact (children element addressWidth (.storage index)).hasStructuralResult
      (storageInputs element addressWidth inputs gateProposals index)
      (currentState (.storage index))
  rcases (Enumeration.fin (EntryCount addressWidth)).exists_pi
      StorageProperty storesAvailable with ⟨storageProposals, storageSatisfies⟩
  rcases (children element addressWidth .combine).hasStructuralResult
      (combineInputs element addressWidth storageProposals) (currentState .combine) with
    ⟨combineProposal, combineSatisfies⟩
  rcases (children element addressWidth .readMux).hasStructuralResult
      (muxInputs element addressWidth inputs combineProposal) (currentState .readMux) with
    ⟨muxProposal, muxSatisfies⟩
  let childProposals : (child : Instance addressWidth) →
      ProposedValues (childStructure element addressWidth child)
    | .decoder => decoderProposal
    | .decodeSplit => splitProposal
    | .gate index => gateProposals index
    | .storage index => storageProposals index
    | .combine => combineProposal
    | .readMux => muxProposal
  let outputs : (ports element addressWidth).outputs.Values := fun
    | .readValue => muxProposal.outputs .result
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | decoder =>
      change (children element addressWidth decoder).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals decoder)
        (currentState decoder) decoderProposal
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals decoder =
          decoderInputs element addressWidth inputs by funext port; cases port; rfl]
      exact decoderSatisfies
    | decodeSplit =>
      change (children element addressWidth decodeSplit).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals decodeSplit)
        (currentState decodeSplit) splitProposal
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals decodeSplit =
          splitInputs addressWidth decoderProposal by funext port; cases port; rfl]
      exact splitSatisfies
    | gate index =>
      change (children element addressWidth (gate index)).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals (gate index))
        (currentState (gate index)) (gateProposals index)
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals (gate index) =
          gateInputs element addressWidth inputs splitProposal index by
            funext port; cases port <;> rfl]
      exact gateSatisfies index
    | storage index =>
      change (children element addressWidth (storage index)).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals (storage index))
        (currentState (storage index)) (storageProposals index)
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals (storage index) =
          storageInputs element addressWidth inputs gateProposals index by
            funext port; cases port <;> rfl]
      exact storageSatisfies index
    | combine =>
      change (children element addressWidth combine).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals combine)
        (currentState combine) combineProposal
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals combine =
          combineInputs element addressWidth storageProposals by funext port; rfl]
      exact combineSatisfies
    | readMux =>
      change (children element addressWidth readMux).moduleStructure.IsSolution
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals readMux)
        (currentState readMux) muxProposal
      rw [show ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs childProposals readMux =
          muxInputs element addressWidth inputs combineProposal by
            funext port; cases port <;> rfl]
      exact muxSatisfies

def stateCorresponds (element : SignalType) (addressWidth : Nat)
    (contractState : (stateMap element addressWidth).Values)
    (structuralState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) : Prop :=
  ∀ index : Fin (EntryCount addressWidth),
    (children element addressWidth (storage index)).stateCorresponds
      (fun | .stored => contractState .entries index)
      (structuralState (storage index))

private theorem hasCorrespondingState (element : SignalType) (addressWidth : Nat)
    (structuralState : (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)).State) :
    ∃ contractState, stateCorresponds element addressWidth contractState structuralState := by
  let Property := fun index contractState =>
    (children element addressWidth (storage index)).stateCorresponds contractState
      (structuralState (storage index))
  have available : ∀ index, ∃ contractState, Property index contractState := by
    intro index
    exact (children element addressWidth (storage index)).hasCorrespondingState
      (structuralState (storage index))
  rcases (Enumeration.fin (EntryCount addressWidth)).exists_pi Property available with
    ⟨states, corresponds⟩
  let contractState : (stateMap element addressWidth).Values := fun
    | .entries => fun index => states index .stored
  exact ⟨contractState, fun index => corresponds index⟩

private theorem implements (element : SignalType) (addressWidth : Nat) :
    Implements (Certified.moduleStructure (body element addressWidth)
      (children element addressWidth)) (cycleContract element addressWidth)
      (stateCorresponds element addressWidth) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches : ∀ index : Fin (EntryCount addressWidth),
      (children element addressWidth (storage index)).cycleContract.EvaluatesTo
        (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposal.2 (storage index))
        (fun | .stored => contractState .entries index)
        (proposal.2 (storage index)).outputs
        ((children element addressWidth (storage index)).cycleContract.stateRule.apply
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index)) ∧
      (children element addressWidth (storage index)).stateCorresponds
        ((children element addressWidth (storage index)).cycleContract.stateRule.apply
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index))
        (proposal.2 (storage index)).nextState := by
    intro index
    exact Certified.childSolutionMatchesContract (children element addressWidth)
      inputs structuralState proposal satisfies (storage index)
      (fun | .stored => contractState .entries index) (corresponds index)
  have storageCurrent : ∀ index : Fin (EntryCount addressWidth),
      (proposal.2 (storage index)).outputs .value = contractState .entries index := by
    intro index
    exact (EnabledRegister.outputRule_holds_iff element _ _ _).mp
      ((storageMatches index).1.1 EnabledRegister.Rule.observe)

  rcases (children element addressWidth decoder).hasCorrespondingState
      (structuralState decoder) with ⟨decoderState, decoderCorresponds⟩
  have decoderState_eq : decoderState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst decoderState
  have decoderMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies decoder
    SignalMap.emptyValues decoderCorresponds
  have decoderValue (index : Fin (EntryCount addressWidth)) :
      (proposal.2 decoder).outputs .result index =
        BinaryToOneHot.oneHot addressWidth (inputs .writeAddress) index := by
    have held := decoderMatches.1.1 BinaryToOneHot.Rule.apply
    have result := BinaryToOneHot.result_of_holds addressWidth _ _ _ held index
    rw [show (ProposedValues.childInputs (body element addressWidth)
        (childStructure element addressWidth) inputs proposal.2 decoder) .value =
        inputs .writeAddress by rfl] at result
    exact result

  rcases (children element addressWidth decodeSplit).hasCorrespondingState
      (structuralState decodeSplit) with ⟨splitState, splitCorresponds⟩
  have splitState_eq : splitState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst splitState
  have splitMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies decodeSplit
    SignalMap.emptyValues splitCorresponds
  have splitValue (index : Fin (EntryCount addressWidth)) :
      (proposal.2 decodeSplit).outputs index = (proposal.2 decoder).outputs .result index := by
    have equal := (SignalSplitter.outputRule_holds_iff
      (SignalSplitter.vector (EntryCount addressWidth) .bit) _ _ _).mp
      (splitMatches.1.1 SignalComponentRule.apply)
    exact congrFun equal index

  have gateValue (index : Fin (EntryCount addressWidth)) :
      (proposal.2 (gate index)).outputs .output =
        (BinaryToOneHot.oneHot addressWidth (inputs .writeAddress) index &&
          inputs .writeEnable) := by
    have gateMatches := Certified.childSolutionMatchesContract
      (children element addressWidth) inputs structuralState proposal satisfies (gate index)
      SignalMap.emptyValues (by trivial)
    have held := gateMatches.1.1 Primitives.AndRule.apply
    change Primitives.andOutputRule.Holds _ SignalMap.emptyValues _ at held
    rw [Primitives.andOutputRule_holds_iff] at held
    rw [show (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposal.2 (gate index)) .left =
          inputs .writeEnable by rfl,
      show (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposal.2 (gate index)) .right =
          (proposal.2 decodeSplit).outputs index by rfl,
      splitValue index, decoderValue index] at held
    simpa [Bool.and_comm] using held

  rcases (children element addressWidth combine).hasCorrespondingState
      (structuralState combine) with ⟨combineState, combineCorresponds⟩
  have combineState_eq : combineState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst combineState
  have combineMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies combine
    SignalMap.emptyValues combineCorresponds
  have combineValue : (proposal.2 combine).outputs .value =
      fun index => (proposal.2 (storage index)).outputs .value := by
    have equal := (SignalCombiner.outputRule_holds_iff
      (entryCombiner element addressWidth) _ _ _).mp
      (combineMatches.1.1 SignalComponentRule.apply)
    exact congrFun equal AggregatePort.value

  rcases (children element addressWidth readMux).hasCorrespondingState
      (structuralState readMux) with ⟨muxState, muxCorresponds⟩
  have muxState_eq : muxState = SignalMap.emptyValues := by
    funext port; exact nomatch port
  subst muxState
  have muxMatches := Certified.childSolutionMatchesContract
    (children element addressWidth) inputs structuralState proposal satisfies readMux
    SignalMap.emptyValues muxCorresponds
  have muxValue : (proposal.2 readMux).outputs .result =
      contractState .entries (BitVector.toIndex addressWidth (inputs .readAddress)) := by
    have held := muxMatches.1.1 CombMuxTree.Rule.apply
    change (CombMuxTree.outputRule element addressWidth).Holds
      (ProposedValues.childInputs (body element addressWidth)
        (childStructure element addressWidth) inputs proposal.2 readMux)
      SignalMap.emptyValues (proposal.2 readMux).outputs at held
    rw [CombMuxTree.outputRule_holds_iff] at held
    rw [show (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposal.2 readMux) .values =
          (proposal.2 combine).outputs .value by rfl,
      show (ProposedValues.childInputs (body element addressWidth)
          (childStructure element addressWidth) inputs proposal.2 readMux) .index =
          inputs .readAddress by rfl] at held
    rw [held]
    unfold CombMuxTree.select
    change (proposal.2 combine).outputs .value
      (BitVector.toIndex addressWidth (inputs .readAddress)) = _
    rw [combineValue]
    change (proposal.2 (storage (BitVector.toIndex addressWidth
      (inputs .readAddress)))).outputs .value = _
    exact storageCurrent _

  let nextContractState : (stateMap element addressWidth).Values := fun
    | .entries => nextEntries addressWidth (inputs .writeEnable)
        (inputs .writeAddress) (inputs .writeValue) (contractState .entries)
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [readRule_holds_iff]
      exact (satisfies.1 .readValue).trans muxValue
    · rfl
  · intro index
    have nextCorresponds := (storageMatches index).2
    change (children element addressWidth (storage index)).stateCorresponds
      (fun | .stored => nextContractState .entries index)
      (proposal.2 (storage index)).nextState
    rw [show (fun | .stored => nextContractState .entries index) =
        (children element addressWidth (storage index)).cycleContract.stateRule.apply
          (ProposedValues.childInputs (body element addressWidth)
            (childStructure element addressWidth) inputs proposal.2 (storage index))
          (fun | .stored => contractState .entries index) by
      funext statePort
      cases statePort
      simp only [CycleStateRule.apply]
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

private noncomputable def proofCertification (element : SignalType) (addressWidth : Nat) :
    ModuleCycleCertification
      (Certified.moduleStructure (body element addressWidth)
        (children element addressWidth))
      (cycleContract element addressWidth) where
  stateCorresponds := stateCorresponds element addressWidth
  hasCorrespondingState := hasCorrespondingState element addressWidth
  hasStructuralResult := hasStructuralResult element addressWidth
  structuralResultUnique := hasAtMostOneSolution element addressWidth
  implements := implements element addressWidth

noncomputable opaque certification (element : SignalType) (addressWidth : Nat) :
    ModuleCycleCertification (moduleStructure element addressWidth)
      (cycleContract element addressWidth) :=
  (proofCertification element addressWidth).transportStructure
    (moduleStructure_eq element addressWidth).symm

noncomputable def certified (element : SignalType) (addressWidth : Nat) :
    ModuleCycleCertified (ports element addressWidth) :=
  (certification element addressWidth).bundle

@[simp] theorem certified_moduleStructure (element : SignalType) (addressWidth : Nat) :
    (certified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem certified_cycleContract (element : SignalType) (addressWidth : Nat) :
    (certified element addressWidth).cycleContract =
      cycleContract element addressWidth := rfl

theorem hasExactlyOneSolution (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (currentState : (moduleStructure element addressWidth).State) :
    ∃ proposal,
      (moduleStructure element addressWidth).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure element addressWidth).IsSolution
        inputs currentState other → other = proposal :=
  (certified element addressWidth).hasExactlyOneStructuralResult inputs currentState

@[simp] theorem stateRule_apply_entries (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth).apply inputs state .entries =
      nextEntries addressWidth (inputs .writeEnable) (inputs .writeAddress)
        (inputs .writeValue) (state .entries) := by
  rfl

theorem readValue_of_evaluatesTo (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth).EvaluatesTo
      inputs state outputs nextState) :
    outputs .readValue =
      state .entries (BitVector.toIndex addressWidth (inputs .readAddress)) :=
  (readRule_holds_iff element addressWidth inputs state outputs).mp
    (evaluates.1 .read)

theorem written_entry_of_evaluatesTo (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth).EvaluatesTo
      inputs state outputs nextState)
    (enabled : inputs .writeEnable = true) :
    nextState .entries (BitVector.toIndex addressWidth (inputs .writeAddress)) =
      inputs .writeValue := by
  rw [evaluates.2, stateRule_apply_entries, enabled]
  exact nextEntries_selected _ _ _ _

theorem retained_entry_of_evaluatesTo (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element addressWidth).inputs.Values)
    (state : (stateMap element addressWidth).Values)
    (outputs : (ports element addressWidth).outputs.Values)
    (nextState : (stateMap element addressWidth).Values)
    (evaluates : (cycleContract element addressWidth).EvaluatesTo
      inputs state outputs nextState)
    (index : Fin (EntryCount addressWidth))
    (different : index ≠ BitVector.toIndex addressWidth (inputs .writeAddress)) :
    nextState .entries index = state .entries index := by
  rw [evaluates.2, stateRule_apply_entries]
  exact nextEntries_other _ _ _ _ _ _ different

end Silean2.Modules.RegisterBank

namespace Silean2.Modules.RegisterBank.Naming

open Silean2 Silean2.Naming

def portsWithNaming (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.RegisterBank.ports element addressWidth) where
  inputs := ⟨fun
    | .writeEnable => "write_enable"
    | .writeAddress => "write_address"
    | .writeValue => "write_value"
    | .readAddress => "read_address"⟩
  outputs := ⟨fun | .readValue => "read_value"⟩
  inputTypes := fun
    | .writeEnable => .bit
    | .writeAddress | .readAddress => .vector .bit
    | .writeValue => elementNaming
  outputTypes := fun | .readValue => elementNaming

def ports (element : SignalType) (addressWidth : Nat) :
    ModulePortsNaming (Modules.RegisterBank.ports element addressWidth) :=
  portsWithNaming element addressWidth (.positional element)

def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth) := by
  unfold Modules.RegisterBank.moduleStructure
  exact .composite ⟨"register_bank", "structural",
      [.shape element, .natural addressWidth]⟩
    (portsWithNaming element addressWidth elementNaming)
    (fun
      | .decoder => "write_decoder"
      | .decodeSplit => "write_decoder_split"
      | .gate index => s!"write_gate_{index.val}"
      | .storage index => s!"entry_{index.val}"
      | .combine => "entries"
      | .readMux => "read_mux")
    (fun
      | .decoder => BinaryToOneHot.Naming.naming addressWidth
      | .decodeSplit => Silean2.Naming.SignalAdapter.splitter
          (.vector (Modules.RegisterBank.EntryCount addressWidth) .bit)
      | .gate _ => Silean2.Naming.Primitive.and
      | .storage _ =>
          EnabledRegister.Naming.namingWith element elementNaming
      | .combine =>
          Silean2.Naming.SignalAdapter.combiner
            (.vector (Modules.RegisterBank.EntryCount addressWidth) element)
      | .readMux =>
          CombMuxTree.Naming.namingWith element addressWidth elementNaming)

def naming (element : SignalType) (addressWidth : Nat) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth) :=
  namingWith element addressWidth (.positional element)

end Silean2.Modules.RegisterBank.Naming
