import Silean.Modules.CarrySaveLayer.CarrySaveLayerDerived
import Silean.Modules.CarrySaveTree.CarrySaveTree
import Silean.Modules.Constant.Constant
import Silean.Naming.SignalAdapterNaming

/-! Recursive structural implementation of the carry-save tree. -/

namespace Silean.Modules.CarrySaveTree.Internal

open Silean

def zeroValue (width : Nat) : Fin width → Bool :=
  BitVector.ofNat width 0

@[reducible] def inputSplitter (width operandCount : Nat) :
    Composition.SignalSplitter :=
  .vector operandCount (.vector width .bit)

inductive ZeroInstance | split | zeroA | zeroB
deriving Enumeration

@[reducible] def zeroInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of ZeroInstance fun
    | .split => (inputSplitter width 0).ports
    | .zeroA | .zeroB => Modules.Constant.ports (.vector width .bit)

@[reducible] def zeroContext (width : Nat) : EndpointContext where
  ports := ports width 0
  instancePorts := zeroInstances width

@[reducible] def zeroWiring (width : Nat) :
    Wiring (zeroContext width).ports (zeroContext width).instancePorts :=
  let context := zeroContext width
  { moduleOutput := fun
      | .resultA => context.instanceOutput .zeroA .output
      | .resultB => context.instanceOutput .zeroB .output
    instanceInput := fun
      | .split, .value => context.moduleInput .operands
      | .zeroA, impossible | .zeroB, impossible => nomatch impossible }

@[reducible] def zeroBody (width : Nat) : ModuleBody :=
  ⟨zeroContext width, zeroWiring width⟩

@[reducible] def zeroStructure (width : Nat) : ModuleStructure (ports width 0) :=
  .composite (zeroBody width) fun
    | .split => .splitter (inputSplitter width 0)
    | .zeroA | .zeroB =>
        Modules.Constant.moduleStructure (.vector width .bit) (zeroValue width)

inductive OneInstance | split | zero
deriving Enumeration

@[reducible] def oneInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of OneInstance fun
    | .split => (inputSplitter width 1).ports
    | .zero => Modules.Constant.ports (.vector width .bit)

@[reducible] def oneContext (width : Nat) : EndpointContext where
  ports := ports width 1
  instancePorts := oneInstances width

@[reducible] def oneWiring (width : Nat) :
    Wiring (oneContext width).ports (oneContext width).instancePorts :=
  let context := oneContext width
  { moduleOutput := fun
      | .resultA => context.instanceOutput .split 0
      | .resultB => context.instanceOutput .zero .output
    instanceInput := fun
      | .split, .value => context.moduleInput .operands
      | .zero, impossible => nomatch impossible }

@[reducible] def oneBody (width : Nat) : ModuleBody :=
  ⟨oneContext width, oneWiring width⟩

@[reducible] def oneStructure (width : Nat) : ModuleStructure (ports width 1) :=
  .composite (oneBody width) fun
    | .split => .splitter (inputSplitter width 1)
    | .zero =>
        Modules.Constant.moduleStructure (.vector width .bit) (zeroValue width)

inductive TwoInstance | split
deriving Enumeration

@[reducible] def twoInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of TwoInstance fun
    | .split => (inputSplitter width 2).ports

@[reducible] def twoContext (width : Nat) : EndpointContext where
  ports := ports width 2
  instancePorts := twoInstances width

@[reducible] def twoWiring (width : Nat) :
    Wiring (twoContext width).ports (twoContext width).instancePorts :=
  let context := twoContext width
  { moduleOutput := fun
      | .resultA => context.instanceOutput .split 0
      | .resultB => context.instanceOutput .split 1
    instanceInput := fun
      | .split, .value => context.moduleInput .operands }

@[reducible] def twoBody (width : Nat) : ModuleBody :=
  ⟨twoContext width, twoWiring width⟩

@[reducible] def twoStructure (width : Nat) : ModuleStructure (ports width 2) :=
  .composite (twoBody width) fun
    | .split => .splitter (inputSplitter width 2)

inductive RecursiveInstance | layer | rest
deriving Enumeration

@[reducible] def recursiveInstances (width operandCount : Nat) : InstancePorts :=
  EnumeratedMap.of RecursiveInstance fun
    | .layer => CarrySaveLayer.ports width operandCount
    | .rest => ports width (CarrySaveLayer.reducedCount operandCount)

@[reducible] def recursiveContext (width operandCount : Nat) : EndpointContext where
  ports := ports width operandCount
  instancePorts := recursiveInstances width operandCount

@[reducible] def recursiveWiring (width operandCount : Nat) :
    Wiring (recursiveContext width operandCount).ports
      (recursiveContext width operandCount).instancePorts :=
  let context := recursiveContext width operandCount
  { moduleOutput := fun
      | .resultA => context.instanceOutput .rest .resultA
      | .resultB => context.instanceOutput .rest .resultB
    instanceInput := fun
      | .layer, .operands => context.moduleInput .operands
      | .rest, .operands => context.instanceOutput .layer .reduced }

@[reducible] def recursiveBody (width operandCount : Nat) : ModuleBody :=
  ⟨recursiveContext width operandCount, recursiveWiring width operandCount⟩

@[reducible] def moduleStructure (width : Nat) :
    (operandCount : Nat) → ModuleStructure (ports width operandCount)
  | 0 => zeroStructure width
  | 1 => oneStructure width
  | 2 => twoStructure width
  | operandCount + 3 =>
      .composite (recursiveBody width (operandCount + 3)) fun
        | .layer => CarrySaveLayer.moduleStructure width (operandCount + 3)
        | .rest => moduleStructure width
            (CarrySaveLayer.reducedCount (operandCount + 3))
termination_by operandCount => operandCount
decreasing_by
  exact CarrySaveLayer.reducedCount_lt (operandCount + 3) (by omega)

end Silean.Modules.CarrySaveTree.Internal

namespace Silean.Modules.CarrySaveTree.Naming

open Silean Silean.Naming

def naming (width : Nat) : (operandCount : Nat) →
    ModuleNaming (Internal.moduleStructure width operandCount)
  | 0 => by
      rw [Internal.moduleStructure.eq_def]
      exact .composite ⟨"carry_save_tree", "zero", [.natural width, .natural 0]⟩
        (ports width 0)
        (fun | .split => "split" | .zeroA => "zero_a" | .zeroB => "zero_b")
        (fun
          | .split => SignalAdapter.splitter (Internal.inputSplitter width 0)
          | .zeroA | .zeroB =>
              Modules.Constant.Naming.naming (.vector width .bit)
                (Internal.zeroValue width))
  | 1 => by
      rw [Internal.moduleStructure.eq_def]
      exact .composite ⟨"carry_save_tree", "one", [.natural width, .natural 1]⟩
        (ports width 1)
        (fun | .split => "split" | .zero => "zero")
        (fun
          | .split => SignalAdapter.splitter (Internal.inputSplitter width 1)
          | .zero => Modules.Constant.Naming.naming (.vector width .bit)
              (Internal.zeroValue width))
  | 2 => by
      rw [Internal.moduleStructure.eq_def]
      exact .composite ⟨"carry_save_tree", "two", [.natural width, .natural 2]⟩
        (ports width 2)
        (fun | .split => "split")
        (fun | .split => SignalAdapter.splitter (Internal.inputSplitter width 2))
  | operandCount + 3 => by
      rw [Internal.moduleStructure.eq_def]
      exact .composite
        ⟨"carry_save_tree", "recursive",
          [.natural width, .natural (operandCount + 3)]⟩
        (ports width (operandCount + 3))
        (fun | .layer => "layer" | .rest => "rest")
        (fun
          | .layer => CarrySaveLayer.naming width (operandCount + 3)
          | .rest => naming width
              (CarrySaveLayer.reducedCount (operandCount + 3)))
termination_by operandCount => operandCount
decreasing_by
  exact CarrySaveLayer.reducedCount_lt (operandCount + 3) (by omega)

end Silean.Modules.CarrySaveTree.Naming

namespace Silean.Modules.CarrySaveTree

open Silean

@[reducible] def moduleStructure (width operandCount : Nat) :
    ModuleStructure (ports width operandCount) :=
  Internal.moduleStructure width operandCount

def naming (width operandCount : Nat) :
    Silean.Naming.ModuleNaming (moduleStructure width operandCount) :=
  Naming.naming width operandCount

@[reducible] def design (width operandCount : Nat) : Naming.NamedModule where
  ports := ports width operandCount
  moduleStructure := moduleStructure width operandCount
  naming := naming width operandCount

end Silean.Modules.CarrySaveTree
