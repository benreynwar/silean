import PicoRV.Internal.RegsVerification

/-! Public register-file declarations backed by generated internals. -/

namespace PicoRV.Regs

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn : Net .bit) (decodedRs1 decodedRs2 : Net addressType)
    (cpuregsWrite : Net .bit) (latchedRd : Net addressType)
    (cpuregsWrdata : Net wordType) : Builder ports.OutputNets :=
  ports.placeNamed name moduleStructure naming resetn decodedRs1 decodedRs2
    cpuregsWrite latchedRd cpuregsWrdata

noncomputable def place
    (resetn : Net .bit) (decodedRs1 decodedRs2 : Net addressType)
    (cpuregsWrite : Net .bit) (latchedRd : Net addressType)
    (cpuregsWrdata : Net wordType) : Builder ports.OutputNets :=
  ports.placeIndexed "regs" moduleStructure naming resetn decodedRs1 decodedRs2
    cpuregsWrite latchedRd cpuregsWrdata

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored register-file
construction implements its exact cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

end PicoRV.Regs
