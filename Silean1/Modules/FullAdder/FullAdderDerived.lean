import Silean.Modules.FullAdder.Internal.FullAdderVerification

/-! Public full-adder declarations backed by generated internals. -/

namespace Silean.Modules.FullAdder

open Authoring.CircuitDescription

/-- Place a full adder using the next conventional indexed name. -/
noncomputable def place (left right carryIn : Net .bit) : Builder ports.OutputNets :=
  ports.placeIndexed "full_adder" moduleStructure naming left right carryIn

attribute [circuit_description] place

/-- Every typed implementation corresponding to the authored construction
implements its cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

end Silean.Modules.FullAdder

namespace Silean.Authoring

open CircuitDescription

/-- Place a full adder and return its sum and carry nets. -/
noncomputable abbrev fullAdder (left right carryIn : Net .bit) :
    Builder Modules.FullAdder.ports.OutputNets :=
  Modules.FullAdder.place left right carryIn

attribute [circuit_description] fullAdder

end Silean.Authoring
