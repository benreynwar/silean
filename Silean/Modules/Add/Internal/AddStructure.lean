import Silean.Modules.Add.Add
import Silean.Modules.Constant.Constant
import Silean.Modules.FullAdder.FullAdderDerived
import Silean.Modules.VectorConcat.VectorConcatDerived
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Add

open Silean

def emptyValue : (SignalType.vector 0 .bit).Denote :=
  fun index => Fin.elim0 index

inductive BaseInstance | empty
deriving Enumeration

@[reducible] def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .empty => Modules.Constant.ports (.vector 0 .bit)

@[reducible] def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput
    | .result => baseContext.instanceOutput .empty .output
    | .carryOut => baseContext.moduleInput .carryIn
  instanceInput | .empty, impossible => nomatch impossible

@[reducible] def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .empty => Modules.Constant.moduleStructure (.vector 0 .bit) emptyValue

def operandSplitter (width : Nat) : Composition.SignalSplitter :=
  .vector (width + 1) .bit

def lowerCombiner (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

def highCombiner : Composition.SignalCombiner := .vector 1 .bit

def highIndex (width : Nat) : (operandSplitter width).ports.outputs.Label :=
  Fin.last width

inductive SuccInstance
  | leftSplit
  | rightSplit
  | lowerLeft
  | lowerRight
  | lowerAdd
  | highAdder
  | highBit
  | concat
deriving Enumeration

@[reducible] def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .leftSplit => (operandSplitter width).ports
    | .rightSplit => (operandSplitter width).ports
    | .lowerLeft => (lowerCombiner width).ports
    | .lowerRight => (lowerCombiner width).ports
    | .lowerAdd => ports width
    | .highAdder => FullAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    | .result => (succContext width).instanceOutput .concat .result
    | .carryOut => (succContext width).instanceOutput .highAdder .carryOut
  instanceInput
    | .leftSplit, .value => (succContext width).moduleInput .left
    | .rightSplit, .value => (succContext width).moduleInput .right
    | .lowerLeft, index =>
        (succContext width).instanceOutput .leftSplit index.castSucc
    | .lowerRight, index =>
        (succContext width).instanceOutput .rightSplit index.castSucc
    | .lowerAdd, .left =>
        (succContext width).instanceOutput .lowerLeft .value
    | .lowerAdd, .right =>
        (succContext width).instanceOutput .lowerRight .value
    | .lowerAdd, .carryIn => (succContext width).moduleInput .carryIn
    | .highAdder, .left =>
        (succContext width).instanceOutput .leftSplit (highIndex width)
    | .highAdder, .right =>
        (succContext width).instanceOutput .rightSplit (highIndex width)
    | .highAdder, .carryIn =>
        (succContext width).instanceOutput .lowerAdd .carryOut
    | .highBit, _ => (succContext width).instanceOutput .highAdder .sum
    | .concat, .left =>
        (succContext width).instanceOutput .lowerAdd .result
    | .concat, .right => (succContext width).instanceOutput .highBit .value

@[reducible] def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

/-- Recursive ripple-carry hierarchy with one full adder per bit. -/
def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .leftSplit => .splitter (operandSplitter width)
      | .rightSplit => .splitter (operandSplitter width)
      | .lowerLeft => .combiner (lowerCombiner width)
      | .lowerRight => .combiner (lowerCombiner width)
      | .lowerAdd => moduleStructure width
      | .highAdder => FullAdder.moduleStructure
      | .highBit => .combiner highCombiner
      | .concat => VectorConcat.moduleStructure .bit width 1

end Silean.Modules.Add

namespace Silean.Modules.Add.Naming

open Silean Silean.Naming

def naming : (width : Nat) → ModuleNaming (Modules.Add.moduleStructure width)
  | 0 => by
      rw [Modules.Add.moduleStructure.eq_def]
      exact .composite ⟨"add", "base", []⟩ (ports 0)
        (fun | Modules.Add.BaseInstance.empty => "empty")
        (fun
          | Modules.Add.BaseInstance.empty =>
              Modules.Constant.Naming.naming (.vector 0 .bit) Modules.Add.emptyValue)
  | width + 1 => by
      rw [Modules.Add.moduleStructure.eq_def]
      exact .composite
        ⟨"add", "ripple", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .leftSplit => "left_split"
          | .rightSplit => "right_split"
          | .lowerLeft => "left_lower_bits"
          | .lowerRight => "right_lower_bits"
          | .lowerAdd => "add_lower"
          | .highAdder => "add_high_bit"
          | .highBit => "high_bit"
          | .concat => "concat")
        (fun
          | .leftSplit | .rightSplit =>
              Silean.Naming.SignalAdapter.splitter (Modules.Add.operandSplitter width)
          | .lowerLeft =>
              Silean.Naming.SignalAdapter.combiner (Modules.Add.lowerCombiner width)
          | .lowerRight =>
              Silean.Naming.SignalAdapter.combiner (Modules.Add.lowerCombiner width)
          | .lowerAdd => naming width
          | .highAdder => FullAdder.design.naming
          | .highBit => Silean.Naming.SignalAdapter.combiner Modules.Add.highCombiner
          | .concat => VectorConcat.naming .bit width 1)

end Silean.Modules.Add.Naming

namespace Silean.Modules.Add

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

end Silean.Modules.Add
