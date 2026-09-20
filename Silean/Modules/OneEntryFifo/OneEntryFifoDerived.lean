import Silean.Authoring.FifoPorts
import Silean.Modules.OneEntryFifo.Internal.OneEntryFifoFifoVerification

/-! Public one-entry FIFO declarations backed by generated internals. -/

namespace Silean.Modules.OneEntryFifo

open Silean
open Authoring.CircuitDescription
open Contracts.Fifo.Cycle

/-- Generated hierarchy naming with a caller-supplied payload schema. -/
def namingWith (signalType : SignalType)
    (typeNaming : Naming.SignalTypeNaming signalType) :
    Naming.ModuleNaming (moduleStructure signalType) :=
  (naming signalType).withPorts
    (Naming.FifoPorts.portsWithNaming signalType typeNaming)

/-- Place a one-entry FIFO under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (inputValid : Net .bit) (inputData : Net signalType)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets signalType) :=
  Silean.Interfaces.Fifo.ports.placeNamed signalType name
    (moduleStructure signalType) (naming signalType)
    inputValid inputData outputReady reset

/-- Place a one-entry FIFO using the next conventional indexed name. -/
noncomputable def place (inputValid : Net .bit) (inputData : Net signalType)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets signalType) :=
  Silean.Interfaces.Fifo.ports.placeIndexed signalType "one_entry_fifo"
    (moduleStructure signalType) (naming signalType)
    inputValid inputData outputReady reset

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored construction
implements the exact cycle contract. -/
theorem construction_correct (signalType : SignalType) :
    (description signalType).ImplementsCycleContract
      (cycleContract signalType) (Naming.FifoPorts.ports signalType) :=
  Internal.construction_correct signalType

/-- The generated hierarchy implements the exact cycle contract. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements (moduleStructure signalType)
      (cycleContract signalType) (certification signalType).stateCorresponds :=
  (certification signalType).implements

/-- The one-entry FIFO packaged for exact-cycle serial composition. -/
noncomputable def oneEntryCertified (signalType : SignalType) :
    CertifiedCycleBehavior signalType where
  cycleBehavior := cycleBehavior signalType
  moduleStructure := moduleStructure signalType
  certification := certification signalType

/-- The exact implementation refines the standard capacity-one FIFO
contract. This is the compositional interface used by larger FIFOs. -/
def fifoRefinement (element : SignalType) :
    Contracts.Fifo.FifoCycleRefinement (certified element)
      (Contracts.Fifo.standardContract element 1) :=
  Internal.cycleRefinement element

/-- The one-entry implementation satisfies the standard capacity-one FIFO
contract. -/
noncomputable def fifoCertified (element : SignalType) :
    Contracts.Fifo.FifoCertified (ports element)
      (Interfaces.Fifo.payloadTypes element) :=
  (fifoRefinement element).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType) :
    (fifoCertified element).moduleStructure = moduleStructure element := rfl

@[simp] theorem fifoCertified_contract (element : SignalType) :
    (fifoCertified element).contract =
      Contracts.Fifo.standardContract element 1 := rfl

end Silean.Modules.OneEntryFifo
