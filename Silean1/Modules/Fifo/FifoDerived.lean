import Silean.Authoring.FifoPorts
import Silean.Modules.Fifo.Internal.FifoCorrespondence
import Silean.Modules.Fifo.Internal.FifoFifoVerification

/-! Public pointer-FIFO declarations backed by generated internals. -/

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo
open Authoring.CircuitDescription

namespace Naming

/-- Attach authored payload names to the FIFO boundary and recursively to its
storage hierarchy without changing the canonical structure. -/
def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : Silean.Naming.SignalTypeNaming element) :
    Silean.Naming.ModuleNaming (moduleStructure element addressWidth) :=
  Internal.namingWith element addressWidth elementNaming

end Naming

/-- Place a FIFO under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (addressWidth : Nat) (inputValid : Net .bit) (inputData : Net element)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets element) :=
  Silean.Interfaces.Fifo.ports.placeNamed element name
    (moduleStructure element addressWidth) (naming element addressWidth)
    inputValid inputData outputReady reset

/-- Place a FIFO using the next conventional indexed name. -/
noncomputable def place (addressWidth : Nat)
    (inputValid : Net .bit) (inputData : Net element)
    (outputReady reset : Net .bit) :
    Builder (Silean.Interfaces.Fifo.ports.OutputNets element) :=
  Silean.Interfaces.Fifo.ports.placeIndexed element "fifo"
    (moduleStructure element addressWidth) (naming element addressWidth)
    inputValid inputData outputReady reset

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored construction
implements the exact cycle contract. -/
theorem construction_correct (element : SignalType) (addressWidth : Nat) :
    (description element addressWidth).ImplementsCycleContract
      (cycleContract element addressWidth)
      (Silean.Naming.FifoPorts.ports element) :=
  Internal.construction_correct element addressWidth

/-- The pointer/register-bank hierarchy implements its exact cycle contract. -/
theorem implements_cycle_contract (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element addressWidth)
      (cycleContract element addressWidth)
      (certification element addressWidth).stateCorresponds :=
  (certification element addressWidth).implements

/-- The implementation satisfies the standard bounded FIFO contract with
capacity `2 ^ addressWidth`. -/
noncomputable def fifoCertified (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Fifo.FifoCertified (ports element) (payloadTypes element) :=
  (Internal.fifoRefinement element addressWidth).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem fifoCertified_contract (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).contract =
      Contracts.Fifo.standardContract element
        (Properties.capacity addressWidth) := rfl

end Silean.Modules.Fifo
