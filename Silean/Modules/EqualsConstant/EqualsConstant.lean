import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A combinational comparison between an input signal and a fixed value. -/

namespace EqualsConstant

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  output result : .bit

end EqualsConstant

module_design EqualsConstant (signalType : SignalType)
    (constant : signalType.Denote)
    (specialization := .signalType signalType ::
      Constant.Naming.parameters signalType constant) where
  boundary (EqualsConstant.ports signalType)
    (naming := EqualsConstant.Naming.ports signalType)
  instances {
    -- Produces the fixed comparison operand.
    constantValue := Constant.design signalType constant,
    -- Compares the input with the fixed operand.
    equality := Equality.design signalType }
  wiring {
    outputs {
      .result := equality.result }
    instance (.constantValue) {}
    instance (.equality) {
      .left := input.value,
      .right := constantValue.output }
  }

end Silean.Modules

namespace Silean.Modules.EqualsConstant

open Silean
open Silean.Authoring

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

theorem result_of_evaluatesTo (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType constant).EvaluatesTo
      inputs state outputs nextState) :
    outputs .result = signalType.equal (inputs .value) constant :=
  (outputRule_holds_iff signalType constant inputs state outputs).mp
    (evaluates.1 .apply)

end Silean.Modules.EqualsConstant
