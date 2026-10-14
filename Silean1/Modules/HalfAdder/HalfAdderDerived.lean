import Silean.Modules.HalfAdder.Internal.HalfAdderVerification

/-! Public half-adder declarations backed by generated internals. -/

namespace Silean.Modules.HalfAdder

open Authoring.CircuitDescription

/-- Place a half adder using the next conventional indexed name. -/
noncomputable def place (left right : Net .bit) : Builder ports.OutputNets :=
  ports.placeIndexed "half_adder" moduleStructure naming left right

attribute [circuit_description] place

/-- Every typed implementation corresponding to the authored construction
implements its cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

end Silean.Modules.HalfAdder

namespace Silean.Authoring

open CircuitDescription

/-- Place a half adder and return its sum and carry nets. -/
noncomputable abbrev halfAdder (left right : Net .bit) :
    Builder Modules.HalfAdder.ports.OutputNets :=
  Modules.HalfAdder.place left right

attribute [circuit_description] halfAdder

end Silean.Authoring
