import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.Mux.Mux
import Silean.Modules.VectorSplit.VectorSplit
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.CombMuxTree

open Silean
open Contracts.Cycle.Certification.Layer

/-! # Combinational mux tree

This recursive tree selects one of `2 ^ indexWidth` values. The base and
successor hardware cases remain ordinary Lean definitions in this file;
recursive certification is in `Internal/CombMuxTreeVerification.lean`, and
public structural guarantees are in `CombMuxTreeTheorems.lean`. -/

inductive Input | values | index
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (indexWidth : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .values => .vector (BinaryToOneHot.size indexWidth) element
    | .index => .vector indexWidth .bit

@[reducible] def outputMap (element : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .result => element

@[reducible] def ports (element : SignalType) (indexWidth : Nat) : ModulePorts :=
  ⟨inputMap element indexWidth, outputMap element⟩

def select (indexWidth : Nat) (values : Fin (BinaryToOneHot.size indexWidth) → α)
    (bits : Fin indexWidth → Bool) : α :=
  values (BitVector.toIndex indexWidth bits)

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element indexWidth) emptySignalMap where
  readsInputs := .all (inputMap element indexWidth)
  writesOutputs := .all (outputMap element)
  target inputs _ := fun
    | .result => select indexWidth (inputs .values) (inputs .index)

@[reducible] def cycleContract (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element indexWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule element indexWidth
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element indexWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element indexWidth).outputs.Values) :
    (outputRule element indexWidth).Holds inputs state outputs ↔
      outputs .result = select indexWidth (inputs .values) (inputs .index) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .result
  · intro equal; funext output; cases output; exact equal

theorem result_of_holds (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element indexWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element indexWidth).outputs.Values)
    (holds : (outputRule element indexWidth).Holds inputs state outputs) :
    outputs .result = inputs .values
      ⟨BitVector.toNat indexWidth (inputs .index),
        BitVector.toNat_lt_cardinality indexWidth (inputs .index)⟩ := by
  rw [(outputRule_holds_iff element indexWidth inputs state outputs).mp holds]
  unfold select
  apply congrArg (inputs .values)
  apply Fin.ext
  exact BitVector.toIndex_val indexWidth (inputs .index)

/-! ## Hardware structure

Width zero has one value and no selector bits. -/

namespace Internal

def baseSplitter (element : SignalType) : Composition.SignalSplitter :=
  .vector 1 element

inductive BaseInstance
  /-- Exposes the sole input value. -/
  | split
deriving Enumeration

@[reducible] def baseInstances (element : SignalType) : InstancePorts :=
  EnumeratedMap.of BaseInstance fun | .split => (baseSplitter element).ports

@[reducible] def baseContext (element : SignalType) : EndpointContext where
  ports := ports element 0
  instancePorts := baseInstances element

def baseWiring (element : SignalType) :
    Wiring (baseContext element).ports (baseContext element).instancePorts where
  moduleOutput | .result => baseContext element |>.instanceOutput .split ⟨0, by omega⟩
  instanceInput | .split, .value => baseContext element |>.moduleInput .values

@[reducible] def baseBody (element : SignalType) : ModuleBody :=
  ⟨baseContext element, baseWiring element⟩

def baseModuleStructure (element : SignalType) :
    ModuleStructure (ports element 0) :=
  .composite (baseBody element) fun
    | .split => .splitter (baseSplitter element)

/-! A successor width partitions values into equal halves and the index into
lower bits/high bit, selects recursively from both halves, then chooses with
`Mux`. -/

def indexSplitter (indexWidth : Nat) : Composition.SignalSplitter :=
  .vector (indexWidth + 1) .bit
def indexLowerCombiner (indexWidth : Nat) : Composition.SignalCombiner :=
  .vector indexWidth .bit
def highIndex (indexWidth : Nat) : (indexSplitter indexWidth).ports.outputs.Label :=
  Fin.last indexWidth

end Internal

open Internal

inductive SuccInstance
  /-- Divides the candidate values into lower and upper halves. -/
  | valuesSplit
  /-- Exposes the selector bits. -/
  | indexSplit
  /-- Rebuilds the lower selector bits for recursive selection. -/
  | indexLower
  /-- Selects recursively from the lower half. -/
  | lower
  /-- Selects recursively from the upper half. -/
  | upper
  /-- Uses the high selector bit to choose between the halves. -/
  | mux
deriving Enumeration

@[reducible] def succInstances (element : SignalType) (indexWidth : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .valuesSplit => VectorSplit.ports element
        (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    | .indexSplit => (indexSplitter indexWidth).ports
    | .indexLower => (indexLowerCombiner indexWidth).ports
    | .lower | .upper => ports element indexWidth
    | .mux => Mux.ports element

@[reducible] def succContext (element : SignalType) (indexWidth : Nat) :
    EndpointContext where
  ports := ports element (indexWidth + 1)
  instancePorts := succInstances element indexWidth

def succWiring (element : SignalType) (indexWidth : Nat) :
    Wiring (succContext element indexWidth).ports
      (succContext element indexWidth).instancePorts where
  moduleOutput | .result => (succContext element indexWidth).instanceOutput .mux .result
  instanceInput
    -- Split the candidates and selector.
    | .valuesSplit, .value =>
        (succContext element indexWidth).moduleInput .values
    | .indexSplit, .value =>
        (succContext element indexWidth).moduleInput .index
    | .indexLower, lowerIndex =>
        (succContext element indexWidth).instanceOutput .indexSplit lowerIndex.castSucc
    -- Both recursive muxes use the same lower selector bits.
    | .lower, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .left
    | .lower, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
    | .upper, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .right
    | .upper, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
    -- The high selector bit chooses the recursive result.
    | .mux, .select =>
        (succContext element indexWidth).instanceOutput .indexSplit (highIndex indexWidth)
    | .mux, .whenFalse =>
        (succContext element indexWidth).instanceOutput .lower .result
    | .mux, .whenTrue =>
        (succContext element indexWidth).instanceOutput .upper .result

@[reducible] def succBody (element : SignalType) (indexWidth : Nat) : ModuleBody :=
  ⟨succContext element indexWidth, succWiring element indexWidth⟩

def moduleStructure (element : SignalType) : (indexWidth : Nat) →
    ModuleStructure (ports element indexWidth)
  | 0 => baseModuleStructure element
  | indexWidth + 1 => .composite (succBody element indexWidth) fun
      | .valuesSplit => VectorSplit.moduleStructure element
          (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
      | .indexSplit => .splitter (indexSplitter indexWidth)
      | .indexLower => .combiner (indexLowerCombiner indexWidth)
      | .lower | .upper => moduleStructure element indexWidth
      | .mux => Mux.moduleStructure element


end Silean.Modules.CombMuxTree

namespace Silean.Modules.CombMuxTree.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (indexWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.CombMuxTree.ports element indexWidth) where
  inputs := ⟨fun | .values => "values" | .index => "index"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .values => .vector elementNaming
    | .index => .vector .bit
  outputTypes := fun | .result => elementNaming

def ports (element : SignalType) (indexWidth : Nat) :
    ModulePortsNaming (Modules.CombMuxTree.ports element indexWidth) :=
  portsWithNaming element indexWidth (.positional element)

def namingWith (element : SignalType) : (indexWidth : Nat) →
    SignalTypeNaming element →
      ModuleNaming (Modules.CombMuxTree.moduleStructure element indexWidth)
  | 0, elementNaming => by
      rw [Modules.CombMuxTree.moduleStructure.eq_def]
      exact .composite
        ⟨"comb_mux_tree", "base", [.signalType element]⟩
        (portsWithNaming element 0 elementNaming)
        (fun | Modules.CombMuxTree.Internal.BaseInstance.split => "split_value")
        (fun
          | Modules.CombMuxTree.Internal.BaseInstance.split =>
              Silean.Naming.SignalAdapter.splitterWithNaming
                (Composition.SignalSplitter.vector 1 element)
                (SignalTypeNaming.vector elementNaming))
  | indexWidth + 1, elementNaming => by
      rw [Modules.CombMuxTree.moduleStructure.eq_def]
      exact .composite
        ⟨"comb_mux_tree", "recursive", [.signalType element, .natural (indexWidth + 1)]⟩
        (portsWithNaming element (indexWidth + 1) elementNaming)
        (fun
          | .valuesSplit => "split_values"
          | .indexSplit => "split_index"
          | .indexLower => "combine_index_lower"
          | .lower => "select_lower"
          | .upper => "select_upper"
          | .mux => "mux")
        (fun
          | .valuesSplit => VectorSplit.namingWith element
              (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
              elementNaming
          | .indexSplit => Silean.Naming.SignalAdapter.splitter
              (Modules.CombMuxTree.Internal.indexSplitter indexWidth)
          | .indexLower => Silean.Naming.SignalAdapter.combiner
              (Modules.CombMuxTree.Internal.indexLowerCombiner indexWidth)
          | .lower | .upper => namingWith element indexWidth elementNaming
          | .mux => Mux.naming element)

def naming (element : SignalType) (indexWidth : Nat) :
    ModuleNaming (Modules.CombMuxTree.moduleStructure element indexWidth) :=
  namingWith element indexWidth (.positional element)

end Silean.Modules.CombMuxTree.Naming

namespace Silean.Modules.CombMuxTree

@[reducible] def designWith (element : SignalType) (indexWidth : Nat)
    (elementNaming : Silean.Naming.SignalTypeNaming element) :
    Silean.Naming.NamedModule where
  ports := ports element indexWidth
  moduleStructure := moduleStructure element indexWidth
  naming := Naming.namingWith element indexWidth elementNaming

@[reducible] def design (element : SignalType) (indexWidth : Nat) :
    Silean.Naming.NamedModule :=
  designWith element indexWidth (.positional element)

end Silean.Modules.CombMuxTree
