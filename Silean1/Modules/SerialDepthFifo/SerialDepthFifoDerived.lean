import Silean.Authoring.FifoPorts
import Silean.Modules.SerialDepthFifo.Internal.SerialDepthFifoFifoVerification
import Silean.Naming.FifoSerialNaming

/-! Public serial-depth FIFO declarations backed by recursive internals. -/

namespace Silean.Modules.SerialDepthFifo

open Silean Silean.Naming
open Authoring.CircuitDescription

namespace Naming

open Silean.Naming

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Internal.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => OneEntryFifo.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      Composition.FifoSerial.Naming.serialNamingWith signalType typeNaming
        (additionalDepth + 2)
        (OneEntryFifo.namingWith signalType typeNaming)
        (namingFromAdditional signalType typeNaming additionalDepth)

def depthNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (moduleStructure signalType depth positive) :=
  namingFromAdditional signalType typeNaming (additionalDepth depth)

def depthNaming (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (moduleStructure signalType depth positive) :=
  depthNamingWith signalType (.positional signalType) depth positive

end Naming

/-- The recursively assembled design with authored payload names. -/
@[reducible] def designWith (signalType : SignalType)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) : NamedModule :=
  ⟨Silean.Interfaces.Fifo.ports signalType,
    moduleStructure signalType depth positive,
    Naming.depthNamingWith signalType typeNaming depth positive⟩

/-- The recursively assembled design with positional payload names. -/
@[reducible] def design (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : NamedModule :=
  designWith signalType (.positional signalType) depth positive

/-- Place a positive-depth serial FIFO under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (depth : Nat) (positive : 0 < depth)
    (inputValid : Net .bit) (inputData : Net signalType)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets signalType) :=
  Silean.Interfaces.Fifo.ports.placeNamed signalType name
    (moduleStructure signalType depth positive)
    (Naming.depthNaming signalType depth positive)
    inputValid inputData outputReady reset

/-- Place a positive-depth serial FIFO using the next indexed name. -/
noncomputable def place (depth : Nat) (positive : 0 < depth)
    (inputValid : Net .bit) (inputData : Net signalType)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets signalType) :=
  Silean.Interfaces.Fifo.ports.placeIndexed signalType "serial_depth_fifo"
    (moduleStructure signalType depth positive)
    (Naming.depthNaming signalType depth positive)
    inputValid inputData outputReady reset

attribute [circuit_description] placeNamed place

/-- The recursive hierarchy implements its exact cycle contract. -/
theorem implements_contract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.Implements
      (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive)
      (certification signalType depth positive).stateCorresponds :=
  (certification signalType depth positive).implements

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).moduleStructure =
      moduleStructure signalType depth positive := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).cycleContract =
      cycleContract signalType depth positive := rfl

noncomputable def fifoCertified (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element)
      (Silean.Interfaces.Fifo.payloadTypes element) :=
  Internal.fifoCertified element depth positive

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).moduleStructure =
      moduleStructure element depth positive :=
  Internal.fifoCertified_moduleStructure element depth positive

@[simp] theorem fifoCertified_contract (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).contract =
      Contracts.Fifo.standardContract element depth :=
  Internal.fifoCertified_contract element depth positive

end Silean.Modules.SerialDepthFifo
