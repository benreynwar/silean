import Silean.Composition.BinaryLeafwise
import Silean.Composition.SignalLogic
import Silean.Naming.PrimitiveNaming
import Silean.Naming.BinaryLeafwiseNaming
import Silean.Primitives.And

namespace Silean.Modules.BitwiseAnd

open Silean

/-! Generic bitwise AND, instantiated from the shared certified binary
leafwise construction and the one-bit AND primitive. -/

@[reducible] private def operation : Composition.BinaryLeafwise.Operation where
  apply := SignalType.bitwiseAnd
  split_apply := SignalSplitter.split_bitwiseAnd

@[reducible] private local instance operationInstance :
    Composition.BinaryLeafwise.Operation := operation

@[reducible] private def gate :
    Composition.BinaryLeafwise.BitGate operationInstance where
  cycleContract := Primitives.andCycleContract
  certified := Primitives.andCertified.certifiedStructure
  rule := .apply
  everyRule := by intro candidate; cases candidate; rfl
  reads := rfl
  writes := rfl
  state := SignalMap.emptyValues
  stateSubsingleton := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  stateReadsEmpty := rfl
  output_eq := fun inputs state outputs holds =>
    (Primitives.andOutputRule_holds_iff inputs state outputs).mp holds

@[reducible] private local instance gateInstance :
    Composition.BinaryLeafwise.BitGate operationInstance := gate

abbrev Input := Composition.BinaryLeafwise.Input
abbrev Output := Composition.BinaryLeafwise.Output
abbrev Rule := Composition.BinaryLeafwise.Rule
namespace Input
abbrev left : Input := Composition.BinaryLeafwise.Input.left
abbrev right : Input := Composition.BinaryLeafwise.Input.right
end Input
namespace Output
abbrev result : Output := Composition.BinaryLeafwise.Output.result
end Output
namespace Rule
abbrev apply : Rule := Composition.BinaryLeafwise.Rule.apply
end Rule

@[reducible] def ports := Composition.BinaryLeafwise.ports
def outputRule := Composition.BinaryLeafwise.outputRule
@[reducible] def cycleContract := Composition.BinaryLeafwise.cycleContract
def bitModuleStructure := Composition.BinaryLeafwise.bitModuleStructure
def moduleStructure := Composition.BinaryLeafwise.moduleStructure

noncomputable def certified (signalType : SignalType) :=
  Composition.BinaryLeafwise.certified signalType

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.bitwiseAnd (inputs .left) (inputs .right) :=
  Composition.BinaryLeafwise.outputRule_holds_iff signalType inputs state outputs

/-- Contract-facing result law for generic bitwise AND. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = signalType.bitwiseAnd (inputs .left) (inputs .right) :=
  Composition.BinaryLeafwise.result_of_evaluatesTo signalType inputs state outputs
    nextState evaluates

namespace Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :=
  Silean.Naming.BinaryLeafwise.portsWithNaming signalType typeNaming

def ports (signalType : SignalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.BitwiseAnd.moduleStructure signalType) :=
  Silean.Naming.BinaryLeafwise.namingWith "bitwise_and" "and"
    Silean.Naming.Primitive.and signalType typeNaming

def naming (signalType : SignalType) :
    ModuleNaming (Modules.BitwiseAnd.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Naming

end Silean.Modules.BitwiseAnd
