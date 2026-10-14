import Silean.Modules.Fifo.Internal.FifoPointerControlCorrespondence

/-! Public pointer-controller declarations backed by generated internals. -/

namespace Silean.Modules.Fifo.PointerControl

open Silean
open Authoring.CircuitDescription

/-- Place a pointer controller under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (readPointer writePointer : Net (pointerType addressWidth))
    (inputValid outputReady : Net .bit) : Builder (ports.OutputNets addressWidth) :=
  ports.placeNamed addressWidth name (moduleStructure addressWidth)
    (naming addressWidth) readPointer writePointer inputValid outputReady

/-- Place a pointer controller using the next conventional indexed name. -/
noncomputable def place
    (readPointer writePointer : Net (pointerType addressWidth))
    (inputValid outputReady : Net .bit) : Builder (ports.OutputNets addressWidth) :=
  ports.placeIndexed addressWidth "fifo_pointer_control"
    (moduleStructure addressWidth) (naming addressWidth)
    readPointer writePointer inputValid outputReady

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored construction
implements the pointer-control contract. -/
theorem construction_correct (addressWidth : Nat) :
    (description addressWidth).ImplementsCycleContract
      (cycleContract addressWidth) (Naming.ports addressWidth) :=
  Internal.construction_correct addressWidth

/-- The generated pointer-control hierarchy implements its cycle contract. -/
theorem implements_contract (addressWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure addressWidth)
      (cycleContract addressWidth)
      (certification addressWidth).stateCorresponds :=
  (certification addressWidth).implements

end Silean.Modules.Fifo.PointerControl
