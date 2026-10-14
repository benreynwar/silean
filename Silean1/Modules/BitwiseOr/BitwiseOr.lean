import Silean.Composition.BinaryLeafwise
import Silean.Composition.SignalLogic
import Silean.Authoring.CircuitDescription
import Silean.Naming.PrimitiveNaming
import Silean.Naming.BinaryLeafwiseNaming
import Silean.Primitives.Or

namespace Silean.Modules.BitwiseOr

open Silean
open Silean.Authoring.CircuitDescription

/-! Generic bitwise OR, instantiated from the shared certified binary
leafwise construction and the one-bit OR primitive. -/

@[reducible] private def operation : Composition.BinaryLeafwise.Operation where
  apply := SignalType.bitwiseOr
  split_apply := SignalSplitter.split_bitwiseOr

@[reducible] private local instance operationInstance :
    Composition.BinaryLeafwise.Operation := operation

@[reducible] private def gate :
    Composition.BinaryLeafwise.BitGate operationInstance where
  cycleContract := Primitives.orCycleContract
  certified := Primitives.orCertified.certifiedStructure
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
    (Primitives.orOutputRule_holds_iff inputs state outputs).mp holds

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
def moduleStructure (signalType : SignalType) :=
  Composition.BinaryLeafwise.moduleStructure signalType

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (Composition.BinaryLeafwise.certified signalType).certification

noncomputable def certified (signalType : SignalType) :=
  (certification signalType).bundle

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.bitwiseOr (inputs .left) (inputs .right) :=
  Composition.BinaryLeafwise.outputRule_holds_iff signalType inputs state outputs

/-- Contract-facing result law for generic bitwise OR. -/
theorem result_of_allowed (signalType : SignalType)
    {step : (cycleContract signalType).Step}
    (allowed : (cycleContract signalType).Allows step) :
    step.outputs .result =
      signalType.bitwiseOr (step.inputs .left) (step.inputs .right) :=
  (outputRule_holds_iff signalType _ _ _).mp (allowed.1 .apply)

namespace Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :=
  Silean.Naming.BinaryLeafwise.portsWithNaming signalType typeNaming

def ports (signalType : SignalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType) :=
  Silean.Naming.BinaryLeafwise.namingWith "bitwise_or" "or"
    Silean.Naming.Primitive.or signalType typeNaming

def naming (signalType : SignalType) :
    ModuleNaming (Modules.BitwiseOr.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Naming

@[reducible] def designWith (signalType : SignalType)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule :=
  ⟨ports signalType, moduleStructure signalType,
    Naming.namingWith signalType typeNaming⟩

@[reducible] def design (signalType : SignalType) : Silean.Naming.NamedModule :=
  designWith signalType (.positional signalType)

/-- Place a bitwise OR in a circuit description. -/
noncomputable def place (left right : Net signalType) : Builder (Net signalType) := do
  let child ← Authoring.CircuitDescription.placeIndexed "bitwise_or" (design signalType) fun
    | .left => left
    | .right => right
  pure (child .result)

attribute [circuit_description] place

end Silean.Modules.BitwiseOr
