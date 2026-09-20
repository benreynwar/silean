import Silean.Modules.EqualsConstant.Internal.EqualsConstantVerification

/-! Public constant-comparison declarations backed by generated internals. -/

namespace Silean.Modules.EqualsConstant

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-- Place a constant comparison under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (value : Net signalType) (constant : signalType.Denote) :
    Builder (Net .bit) := do
  let outputs ← ports.placeNamed signalType name
    (moduleStructure signalType constant) (naming signalType constant) value
  pure outputs.result

/-- Place a constant comparison using the next conventional indexed name. -/
noncomputable def place (value : Net signalType)
    (constant : signalType.Denote) : Builder (Net .bit) := do
  let outputs ← ports.placeIndexed signalType "equals_constant"
    (moduleStructure signalType constant) (naming signalType constant) value
  pure outputs.result

attribute [circuit_description] placeNamed place

def namingWith {signalType : SignalType} (constant : signalType.Denote)
    (typeNaming : Naming.SignalTypeNaming signalType) :
    Naming.ModuleNaming (moduleStructure signalType constant) :=
  (naming signalType constant).withPorts
    (Naming.portsWithNaming signalType typeNaming)

@[reducible] def designWith {signalType : SignalType}
    (constant : signalType.Denote)
    (typeNaming : Naming.SignalTypeNaming signalType) : Naming.NamedModule :=
  ⟨ports signalType, moduleStructure signalType constant,
    namingWith constant typeNaming⟩

/-- The authored circuit implements the exact comparison contract. -/
theorem construction_correct (signalType : SignalType)
    (constant : signalType.Denote) :
    (description signalType constant).ImplementsCycleContract
      (cycleContract signalType constant) (Naming.ports signalType) :=
  Internal.construction_correct signalType constant

/-- Every realizable boundary step compares the input with the fixed value. -/
theorem result_of_realization (signalType : SignalType)
    (constant : signalType.Denote)
    {step : (moduleStructure signalType constant).Step}
    (realizes : (moduleStructure signalType constant).Realizes step) :
    step.outputs .result = signalType.equal (step.inputs .value) constant := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signalType constant).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signalType constant).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.result signalType constant allowed

/-- The generated hierarchy implements the exact comparison contract. -/
theorem implements_contract (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.Implements (moduleStructure signalType constant)
      (cycleContract signalType constant)
      (certification signalType constant).stateCorresponds :=
  (certification signalType constant).implements

end Silean.Modules.EqualsConstant
