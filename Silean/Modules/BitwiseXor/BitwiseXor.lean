import Silean.Authoring.CircuitDescription
import Silean.Composition.BinaryLeafwise
import Silean.Composition.SignalLogic
import Silean.Naming.PrimitiveNaming
import Silean.Naming.BinaryLeafwiseNaming
import Silean.Primitives.Xor

namespace Silean.Modules.BitwiseXor

open Silean

/-! Generic bitwise XOR, instantiated from the shared certified binary
leafwise construction and the one-bit XOR primitive. The hierarchy follows
the recursive shape of `SignalType`, so the shared `BinaryLeafwise`
construction remains its primary definition instead of being duplicated by a
fixed `CircuitDescription`. -/

@[reducible] private def operation : Composition.BinaryLeafwise.Operation where
  apply := SignalType.bitwiseXor
  split_apply := SignalSplitter.split_bitwiseXor

@[reducible] private local instance operationInstance :
    Composition.BinaryLeafwise.Operation := operation

@[reducible] private def gate :
    Composition.BinaryLeafwise.BitGate operationInstance where
  cycleContract := Primitives.xorCycleContract
  certified := Primitives.xorCertified.certifiedStructure
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
    (Primitives.xorOutputRule_holds_iff inputs state outputs).mp holds

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
      outputs .result = signalType.bitwiseXor (inputs .left) (inputs .right) :=
  Composition.BinaryLeafwise.outputRule_holds_iff signalType inputs state outputs

/-- Contract-facing result law for generic bitwise XOR. -/
theorem result_of_allowed (signalType : SignalType)
    {step : (cycleContract signalType).Step}
    (allowed : (cycleContract signalType).Allows step) :
    step.outputs .result =
      signalType.bitwiseXor (step.inputs .left) (step.inputs .right) :=
  (outputRule_holds_iff signalType _ _ _).mp (allowed.1 .apply)

namespace Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :=
  Silean.Naming.BinaryLeafwise.portsWithNaming signalType typeNaming

def ports (signalType : SignalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.BitwiseXor.moduleStructure signalType) :=
  Silean.Naming.BinaryLeafwise.namingWith "bitwise_xor" "xor"
    Silean.Naming.Primitive.xor signalType typeNaming

def naming (signalType : SignalType) :
    ModuleNaming (Modules.BitwiseXor.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

/-- Recursive implementation details do not change the requested XOR boundary
naming. -/
theorem namingWith_ports (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (namingWith signalType typeNaming).ports =
      portsWithNaming signalType typeNaming := by
  change
    (@Silean.Naming.BinaryLeafwise.namingWith operationInstance gateInstance
      "bitwise_xor" "xor" Silean.Naming.Primitive.xor signalType
      typeNaming).ports = portsWithNaming signalType typeNaming
  rw [@Silean.Naming.BinaryLeafwise.namingWith_ports
    operationInstance gateInstance]
  rfl

/-- Positional XOR naming has the declared positional boundary. -/
theorem naming_ports (signalType : SignalType) :
    (naming signalType).ports = ports signalType :=
  namingWith_ports signalType (.positional signalType)

/-- The emitted boundary names of bitwise XOR are collision-free. -/
theorem portNames_nodup (signalType : SignalType) :
    (naming signalType).ports.names.Nodup := by
  rw [naming_ports]
  exact of_decide_eq_true rfl

end Naming

@[reducible] def designWith (signalType : SignalType)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule :=
  ⟨ports signalType, moduleStructure signalType,
    Naming.namingWith signalType typeNaming⟩

@[reducible] def design (signalType : SignalType) : Silean.Naming.NamedModule :=
  designWith signalType (.positional signalType)

/-- Place a bitwise XOR under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (left right : Authoring.CircuitDescription.Net signalType) :
    Authoring.CircuitDescription.Builder
      (Authoring.CircuitDescription.Net signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType) fun
      | .left => left
      | .right => right
  pure (child .result)

/-- Place a bitwise XOR of two equally typed nets in a circuit description. -/
noncomputable def place (left right : Authoring.CircuitDescription.Net signalType) :
    Authoring.CircuitDescription.Builder
      (Authoring.CircuitDescription.Net signalType) := do
  let child ← Authoring.CircuitDescription.placeIndexed "bitwise_xor"
    (design signalType) fun
      | .left => left
      | .right => right
  pure (child .result)

attribute [circuit_description] placeNamed place

end Silean.Modules.BitwiseXor
