import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality
import Silean.Modules.EqualsConstant.Internal.EqualsConstantStructure

/-! # Comparison with a constant

The authored hardware places one constant source and one structural equality
child. The exact contract states only the resulting comparison. Expanded typed
wiring and certification remain under `Internal/`, while
`EqualsConstantTheorems.lean` is the public proof interface. -/

namespace Silean.Modules.EqualsConstant

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open Authoring.CircuitLogic
open scoped Authoring.CircuitLogic

namespace Description

noncomputable def construction (signalType : SignalType)
    (fixedValue : signalType.Denote) : Builder Unit := do
  let value ← input "value" signalType
  output "result" (← value === (← constant signalType fixedValue))

noncomputable def description (signalType : SignalType)
    (constant : signalType.Denote) : Description :=
  build (construction signalType constant)

end Description

/-! ## Placement -/

/-- Place a constant comparison under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (value : Net signalType) (constant : signalType.Denote) :
    Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType constant) fun | .value => value
  pure (child .result)

/-- Place a constant comparison using the next conventional indexed name. -/
noncomputable def place (value : Net signalType)
    (constant : signalType.Denote) : Builder (Net .bit) := do
  let child ← placeIndexed "equals_constant"
    (design signalType constant) fun | .value => value
  pure (child .result)

attribute [circuit_description] placeNamed place

def namingWith {signalType : SignalType} (constant : signalType.Denote)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.ModuleNaming (moduleStructure signalType constant) :=
  (naming signalType constant).withPorts
    (Naming.portsWithNaming signalType typeNaming)

@[reducible] def designWith {signalType : SignalType}
    (constant : signalType.Denote)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule :=
  ⟨ports signalType, moduleStructure signalType constant,
    namingWith constant typeNaming⟩

def outputRule (signalType : SignalType) (constant : signalType.Denote) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap where
  readsInputs := .all (inputMap signalType)
  writesOutputs := .all (outputMap signalType)
  target inputs _ := fun | .result => signalType.equal (inputs .value) constant

module_cycle_contract cycleContract (signalType : SignalType)
    (constant : signalType.Denote) for ports signalType where
  state := emptySignalMap
  output_rule apply := outputRule signalType constant
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType constant).Holds inputs state outputs ↔
      outputs .result = signalType.equal (inputs .value) constant := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .result
  · intro equal; funext output; cases output; exact equal

theorem output_eq_true_iff_of_holds (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (holds : (outputRule signalType constant).Holds inputs state outputs) :
    outputs .result = true ↔ inputs .value = constant := by
  rw [(outputRule_holds_iff signalType constant inputs state outputs).mp holds]
  exact signalType.equal_eq_true_iff _ _

/-- Contract-facing result law over the shared boundary-step API. -/
theorem result_of_allowed (signalType : SignalType)
    (constant : signalType.Denote)
    {step : (cycleContract signalType constant).Step}
    (allowed : (cycleContract signalType constant).Allows step) :
    step.outputs .result = signalType.equal (step.inputs .value) constant :=
  (outputRule_holds_iff signalType constant step.inputs step.currentState
    step.outputs).mp (allowed.1 .apply)

end Silean.Modules.EqualsConstant
