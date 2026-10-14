import Silean.Modules.CombMuxTree.CombMuxTree
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.VectorSplit.VectorSplitDerived
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.CombMuxTree

open Silean

/-! Recursive typed hierarchy and naming for the mux tree. -/

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
