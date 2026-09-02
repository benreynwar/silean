import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Constant
import Silean.Modules.Equality

namespace Silean.Modules.EqualsConstant

open Silean
open Contracts.Cycle.Certification.Layer

/-! Compares a signal with a fixed value. The structure deliberately reuses
the generic `Constant` and `Equality` modules. -/

inductive Input | value
deriving Enumeration

abbrev Output := Equality.Output

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun | .value => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, Equality.outputMap⟩

abbrev Rule := Equality.Rule

def outputRule (signalType : SignalType) (constant : signalType.Denote) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap
      { inputTypes := .cons signalType .nil, outputTypes := .cons .bit .nil } where
  readsInputs := (inputMap signalType).select .value
  writesOutputs := Equality.outputMap.select .result
  target | (value, ()), _ => (signalType.equal value constant, ())

@[reducible] def cycleContract (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType constant⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType constant).Holds inputs state outputs ↔
      outputs .result = signalType.equal (inputs .value) constant := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

theorem output_eq_true_iff_of_holds (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (holds : (outputRule signalType constant).Holds inputs state outputs) :
    outputs .result = true ↔ inputs .value = constant := by
  rw [(outputRule_holds_iff signalType constant inputs state outputs).mp holds]
  exact signalType.equal_eq_true_iff _ _

/-! ## Hardware structure -/

inductive Instance
  /-- Produces the fixed comparison operand. -/
  | constant
  /-- Compares the module input with that operand. -/
  | equality
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .constant => Constant.ports signalType
    | .equality => Equality.ports signalType

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun | .result => c.instanceOutput .equality .result
    instanceInput := fun
      | .constant, impossible => nomatch impossible
      | .equality, .left => c.moduleInput .value
      | .equality, .right => c.instanceOutput .constant .output }

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] def childContracts (signalType : SignalType)
    (constant : signalType.Denote) : Contracts.Cycle.ChildCycleContracts (body signalType)
  | .constant => Constant.cycleContract signalType constant
  | .equality => Equality.cycleContract signalType

@[reducible] def structuralChildren (signalType : SignalType)
    (constant : signalType.Denote) :
    (child : Instance) → ModuleStructure ((instancePorts signalType).ports child)
  | .constant => Constant.moduleStructure signalType constant
  | .equality => Equality.moduleStructure signalType

@[reducible] noncomputable def certifiedChildren (signalType : SignalType)
    (constant : signalType.Denote) :
    (child : Instance) → Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType constant child)
  | .constant => (Constant.certified signalType constant).certifiedStructure
  | .equality => (Equality.certified signalType).certifiedStructure

def moduleStructure (signalType : SignalType) (constant : signalType.Denote) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType constant)

private abbrev constantOccurrence (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType constant) :=
  ⟨.constant, Primitives.ConstantRule.apply⟩

private abbrev equalityOccurrence (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType constant) :=
  ⟨.equality, Equality.Rule.apply⟩

private def scheduleOrders (signalType : SignalType)
    (constant : signalType.Denote) : ScheduleDerivation.RuleScheduleOrders
      (body signalType) (childContracts signalType constant)
      (cycleContract signalType constant) where
  output | .apply => [constantOccurrence signalType constant,
    equalityOccurrence signalType constant]
  state := []

private def derivedRuleSchedules (signalType : SignalType)
    (constant : signalType.Denote) : ScheduleDerivation.DerivedRuleSchedules
      (body signalType) (childContracts signalType constant)
      (cycleContract signalType constant) := by
  derive_rule_schedules (scheduleOrders signalType constant)

private abbrev ruleSchedules (signalType : SignalType)
    (constant : signalType.Denote) :=
  (derivedRuleSchedules signalType constant).schedules

private theorem coversChildren (signalType : SignalType)
    (constant : signalType.Denote) :
    (ruleSchedules signalType constant).CoversChildren :=
  (derivedRuleSchedules signalType constant).coversChildren

section LayerCertification

variable (signalType : SignalType) (constant : signalType.Denote)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType constant child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signalType) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure signalType constant layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure signalType constant layerChildren)
    (cycleContract signalType constant)
    (stateCorresponds signalType constant layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have childMatch (child : Instance) := by
    letI : Subsingleton ((childContracts signalType constant child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState (ProposedValues.composite outputs proposals)
        satisfies child (by cases child <;> exact SignalMap.emptyValues)
  have constantOutput : (proposals .constant).outputs .output = constant :=
    (Constant.outputRule_holds_iff signalType constant _ _ _).mp
      ((childMatch .constant).1.1 Primitives.ConstantRule.apply)
  have equalityOutput : (proposals .equality).outputs .result =
      signalType.equal (inputs .value) ((proposals .constant).outputs .output) := by
    have held := (Equality.outputRule_holds_iff signalType _ _ _).mp
      ((childMatch .equality).1.1 Equality.Rule.apply)
    have inputsEqual : ProposedValues.childInputs (body signalType)
        (fun name => (layerChildren name).moduleStructure) inputs proposals .equality =
          (fun | .left => inputs .value
               | .right => (proposals .constant).outputs .output) := by
      funext input
      cases input <;> rfl
    change (proposals .equality).outputs .result = signalType.equal
      ((ProposedValues.childInputs (body signalType)
        (fun name => (layerChildren name).moduleStructure)
        inputs proposals .equality) .left)
      ((ProposedValues.childInputs (body signalType)
        (fun name => (layerChildren name).moduleStructure)
        inputs proposals .equality) .right) at held
    rw [inputsEqual] at held
    exact held
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = signalType.equal (inputs .value) constant
    rw [show outputs .result = (proposals .equality).outputs .result by
      exact satisfies.1 .result]
    rw [equalityOutput, constantOutput]
  · rfl

end LayerCertification

noncomputable opaque certifiedLayer (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body signalType)
      (childContracts signalType constant) (cycleContract signalType constant) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType constant) (coversChildren signalType constant)
    (stateCorresponds signalType constant)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (implements signalType constant)

noncomputable def certification (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType constant)
      (cycleContract signalType constant) :=
  (certifiedLayer signalType constant).certifyComposite
    (structuralChildren signalType constant) (certifiedChildren signalType constant)
    (by intro child; cases child <;> rfl)

noncomputable def certified (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType constant).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (constant : signalType.Denote) :
    (certified signalType constant).moduleStructure =
      moduleStructure signalType constant := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (constant : signalType.Denote) :
    (certified signalType constant).cycleContract =
      cycleContract signalType constant := rfl

theorem result_of_evaluatesTo (signalType : SignalType)
    (constant : signalType.Denote)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType constant).EvaluatesTo
      inputs state outputs nextState) :
    outputs .result = signalType.equal (inputs .value) constant :=
  (outputRule_holds_iff signalType constant inputs state outputs).mp
    (evaluates.1 .apply)

end Silean.Modules.EqualsConstant

namespace Silean.Modules.EqualsConstant.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.EqualsConstant.ports signalType) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.EqualsConstant.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (constant : signalType.Denote)
    (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.EqualsConstant.moduleStructure signalType constant) :=
  .composite
    ⟨"equals_constant", "structural",
      .shape signalType :: Constant.Naming.parameters signalType constant⟩
    (portsWithNaming signalType typeNaming)
    (fun | .constant => "constant" | .equality => "equality")
    (fun
      | .constant => Constant.Naming.namingWith signalType constant typeNaming
      | .equality => Equality.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) (constant : signalType.Denote) :
    ModuleNaming (Modules.EqualsConstant.moduleStructure signalType constant) :=
  namingWith signalType constant (.positional signalType)

def namedModule (signalType : SignalType) (constant : signalType.Denote) : NamedModule where
  ports := Modules.EqualsConstant.ports signalType
  moduleStructure := Modules.EqualsConstant.moduleStructure signalType constant
  naming := naming signalType constant

end Silean.Modules.EqualsConstant.Naming
