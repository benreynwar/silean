import PicoRV.Memory.Internal.MemoryLookaheadVerification

/-! Public memory look-ahead declarations backed by generated internals. -/

namespace PicoRV.Memory.Lookahead

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn memDoPrefetch memDoRinst memDoRdata memDoWdata : Net .bit)
    (nextPc regOp1 regOp2 : Net (.vector 32 .bit))
    (memWordsize : Net (.vector 2 .bit)) (current : Net stateType) :
    Builder ports.OutputNets :=
  ports.placeNamed name moduleStructure naming resetn memDoPrefetch memDoRinst
    memDoRdata memDoWdata nextPc regOp1 regOp2 memWordsize current

noncomputable def place
    (resetn memDoPrefetch memDoRinst memDoRdata memDoWdata : Net .bit)
    (nextPc regOp1 regOp2 : Net (.vector 32 .bit))
    (memWordsize : Net (.vector 2 .bit)) (current : Net stateType) :
    Builder ports.OutputNets :=
  ports.placeIndexed "memory_lookahead" moduleStructure naming resetn
    memDoPrefetch memDoRinst memDoRdata memDoWdata nextPc regOp1 regOp2
    memWordsize current

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored look-ahead
construction implements its exact cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

end PicoRV.Memory.Lookahead
