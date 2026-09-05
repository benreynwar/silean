import Silean.Authoring.ModuleDesign
import Silean.Modules.BinaryToOneHot
import Silean.Modules.CombMuxTree
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.RegisterBank

open Silean
open Silean.Authoring

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

namespace ReadRule
inductive Input | address deriving Enumeration
inductive Output | value deriving Enumeration
end ReadRule

namespace WriteRule
inductive Input | enable | address | value deriving Enumeration
end WriteRule

@[reducible] private def readInputs (element : SignalType)
    (addressWidth readCount : Nat) (port : Fin readCount) :
    SignalGroup (inputMap element addressWidth readCount) :=
  SignalGroup.fromLabels (inputMap element addressWidth readCount)
    ReadRule.Input fun | .address => .readAddress port

@[reducible] private def readOutputs (element : SignalType)
    (readCount : Nat) (port : Fin readCount) :
    SignalGroup (outputMap element readCount) :=
  SignalGroup.fromLabels (outputMap element readCount)
    ReadRule.Output fun | .value => .readValue port

@[reducible] private def writeInputs (element : SignalType)
    (addressWidth readCount : Nat) :
    SignalGroup (inputMap element addressWidth readCount) :=
  SignalGroup.fromLabels (inputMap element addressWidth readCount)
    WriteRule.Input fun
      | .enable => .writeEnable
      | .address => .writeAddress
      | .value => .writeValue

def nextEntries (addressWidth : Nat) (writeEnable : Bool)
    (writeAddress : Fin addressWidth → Bool) (writeValue : α)
    (entries : Fin (entryCount addressWidth) → α) :
    Fin (entryCount addressWidth) → α :=
  fun index =>
    if writeEnable && decide (index = BitVector.toIndex addressWidth writeAddress)
    then writeValue
    else entries index

def readRule (element : SignalType) (addressWidth readCount : Nat) (port : Fin readCount) :
    Contracts.Cycle.CycleOutputRule
      (ports element addressWidth readCount) (stateMap element addressWidth) where
  readsInputs := readInputs element addressWidth readCount port
  writesOutputs := readOutputs element readCount port
  target inputs state := fun
    | .value => state .entries (BitVector.toIndex addressWidth (inputs .address))

def stateRule (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.CycleStateRule
      (ports element addressWidth readCount) (stateMap element addressWidth) where
  readsInputs := writeInputs element addressWidth readCount
  target inputs state := fun
    | .entries => nextEntries addressWidth (inputs .enable) (inputs .address)
        (inputs .value) (state .entries)

@[reducible] def cycleContract (element : SignalType) (addressWidth readCount : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element addressWidth readCount) where
  state := stateMap element addressWidth
  RuleName := Rule readCount
  ruleNames := ruleEnumeration readCount
  outputRule | .read port => readRule element addressWidth readCount port
  stateRule := stateRule element addressWidth readCount
  outputCoverage := by
    simp only [readRule, readOutputs, SignalGroup.labels]
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
  unfold readRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext output
    cases output
    exact equal

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

namespace Naming

open Silean.Naming

def portsWithNaming (element : SignalType) (addressWidth readCount : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (ports element addressWidth readCount) where
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
    ModulePortsNaming (RegisterBank.ports element addressWidth readCount) :=
  portsWithNaming element addressWidth readCount (.positional element)

end Naming

/-! ## Hardware structure -/

def entryCombiner (element : SignalType)
    (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector (entryCount addressWidth) element

end Silean.Modules.RegisterBank

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design RegisterBank (element : SignalType) (addressWidth : Nat)
    (readCount : Nat) where
  boundary (RegisterBank.ports element addressWidth readCount)
    (naming := RegisterBank.Naming.ports element addressWidth readCount)
  instances {
    -- Decodes the binary write address into one-hot form.
    decoder := BinaryToOneHot.Naming.namedModule addressWidth,
    -- Exposes the individual one-hot write-select bits.
    decodeSplit :=
      Naming.SignalAdapter.splitterDesign
        (Composition.SignalSplitter.vector (RegisterBank.entryCount addressWidth) .bit),
    -- Combines global write enable with one entry's select bit.
    gate (index : Fin (RegisterBank.entryCount addressWidth) in
        Enumeration.fin (RegisterBank.entryCount addressWidth))
      (name := s!"write_gate_{index.val}") := Primitives.andDesign,
    -- Stores one data entry.
    storage (index : Fin (RegisterBank.entryCount addressWidth) in
        Enumeration.fin (RegisterBank.entryCount addressWidth))
      (name := s!"entry_{index.val}") := EnabledRegister.design element,
    -- Collects all stored entries into a vector.
    combine :=
      Naming.SignalAdapter.combinerDesign
        (RegisterBank.entryCombiner element addressWidth),
    -- Selects the asynchronously read entry.
    readMux (port : Fin readCount in Enumeration.fin readCount)
      (name := s!"read_{port.val}_mux") :=
        CombMuxTree.Naming.namedModule element addressWidth }
  wiring {
    outputs {
      -- Each read mux directly drives its corresponding bank output.
      .readValue port := readMux(port)[.result] }
    -- Decode the write address and expose each one-hot bit.
    instance (.decoder) {
      .value := input.writeAddress }
    instance (.decodeSplit) {
      .value := decoder.result }
    -- Enable only the addressed entry when a write is requested.
    instance (.gate index) {
      .left := input.writeEnable,
      .right := decodeSplit[index] }
    -- Every entry sees the write value; its local gate controls loading.
    instance (.storage index) {
      .data := input.writeValue,
      .enable := gate(index)[.output] }
    -- Collect the entries and select one using the read address.
    instance (.combine) {
      index := storage(index)[.q] }
    instance (.readMux port) {
      .values := combine.value,
      .index := input[.readAddress port] }
  }

end Silean.Modules


namespace Silean.Modules.RegisterBank

open Silean

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

def namingWith (element : SignalType) (addressWidth readCount : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth readCount) := by
  unfold Modules.RegisterBank.moduleStructure
  exact .composite ⟨"RegisterBank", "",
      [.signalType element, .natural addressWidth, .natural readCount]⟩
    (portsWithNaming element addressWidth readCount elementNaming)
    (instanceNames element addressWidth readCount)
    (fun
      | .decoder => BinaryToOneHot.Naming.naming addressWidth
      | .decodeSplit => Silean.Naming.SignalAdapter.splitter
          (.vector (Modules.RegisterBank.entryCount addressWidth) .bit)
      | .gate _ => Silean.Naming.Primitive.and
      | .storage _ =>
          EnabledRegister.namingWith element elementNaming
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
