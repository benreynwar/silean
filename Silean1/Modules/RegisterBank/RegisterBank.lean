import Silean.Authoring.ModuleCycleContract
import Silean.Foundation.BitVector
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Naming.ModuleNaming

namespace Silean.Modules.RegisterBank

open Silean
open Silean.Authoring

/-! # Register bank

The public contract describes a bank of `2 ^ addressWidth` entries with one
synchronous write port and independently addressed combinational read ports.
The indexed generated hierarchy lives under `Internal/`.
-/

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

@[simp] theorem stateRule_apply_entries (element : SignalType) (addressWidth readCount : Nat)
    (inputs : (ports element addressWidth readCount).inputs.Values)
    (state : (stateMap element addressWidth).Values) :
    (stateRule element addressWidth readCount).apply inputs state .entries =
      nextEntries addressWidth (inputs .writeEnable) (inputs .writeAddress)
        (inputs .writeValue) (state .entries) := by
  rfl

/-! ## Consequences of the cycle contract -/

section AllowedStep

variable {element : SignalType} {addressWidth readCount : Nat}
  {step : (cycleContract element addressWidth readCount).Step}
  (allowed : (cycleContract element addressWidth readCount).Allows step)

include allowed

/-- Each read port asynchronously observes the entry selected by its own
address in the current bank state. -/
theorem readValue_of_allowed (port : Fin readCount) :
    step.outputs (.readValue port) =
      step.currentState .entries
        (BitVector.toIndex addressWidth (step.inputs (.readAddress port))) :=
  (readRule_holds_iff element addressWidth readCount port
    step.inputs step.currentState step.outputs).mp
    (allowed.1 (.read port))

/-- The state transition updates exactly the addressed entry when writing and
otherwise retains every entry. -/
theorem next_entries_of_allowed :
    step.nextState .entries =
      nextEntries addressWidth (step.inputs .writeEnable)
        (step.inputs .writeAddress) (step.inputs .writeValue)
        (step.currentState .entries) := by
  rw [allowed.2]
  rfl

/-- An enabled write stores the input value at the selected address. -/
theorem written_entry_of_allowed (enabled : step.inputs .writeEnable = true) :
    step.nextState .entries
        (BitVector.toIndex addressWidth (step.inputs .writeAddress)) =
      step.inputs .writeValue := by
  rw [next_entries_of_allowed allowed, enabled]
  exact nextEntries_selected _ _ _ _

/-- Every entry other than the selected write address is retained. -/
theorem retained_entry_of_allowed
    (index : Fin (entryCount addressWidth))
    (different : index ≠ BitVector.toIndex addressWidth (step.inputs .writeAddress)) :
    step.nextState .entries index = step.currentState .entries index := by
  rw [next_entries_of_allowed allowed]
  exact nextEntries_other _ _ _ _ _ _ different

end AllowedStep

end Silean.Modules.RegisterBank
