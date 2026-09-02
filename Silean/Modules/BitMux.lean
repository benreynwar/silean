import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.PrimitiveNaming
import Silean.Primitives

namespace Silean.Modules.BitMux

open Silean
open Contracts.Cycle.Certification.Layer

/-- A one-bit combinational mux built directly from Boolean gates. -/
inductive Instance
  /-- Produces the complement of `select`. -/
  | invertSelect
  /-- Passes `whenFalse` only when `select` is low. -/
  | chooseFalse
  /-- Passes `whenTrue` only when `select` is high. -/
  | chooseTrue
  /-- Combines the mutually exclusive selected values. -/
  | combine
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .invertSelect => Primitives.not.ports
    | .chooseFalse | .chooseTrue => Primitives.and.ports
    | .combine => Primitives.or.ports

inductive Input
  | select
  | whenFalse
  | whenTrue
deriving Enumeration

inductive Output
  | result
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .select | .whenFalse | .whenTrue => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .result => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    -- The OR gate produces the selected result.
    | .result => context.instanceOutput .combine .output
  instanceInput
    -- Generate the low-select condition.
    | .invertSelect, .input =>
        context.moduleInput .select
    -- Select the false input when select is low.
    | .chooseFalse, .left =>
        context.moduleInput .whenFalse
    | .chooseFalse, .right =>
        context.instanceOutput .invertSelect .output
    -- Select the true input when select is high.
    | .chooseTrue, .left =>
        context.moduleInput .whenTrue
    | .chooseTrue, .right =>
        context.moduleInput .select
    -- Combine the two selected branches.
    | .combine, .left =>
        context.instanceOutput .chooseFalse .output
    | .combine, .right =>
        context.instanceOutput .chooseTrue .output

@[reducible] def body : ModuleBody where
  context := context
  wiring := wiring

end Silean.Modules.BitMux

namespace Silean.Modules.BitMux

open Silean

/-- Contracts required at the four primitive child boundaries.  The schedule
below depends on this interface, not on the concrete primitive structures used
to instantiate it. -/
@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .invertSelect => Primitives.notCycleContract
  | .chooseFalse | .chooseTrue => Primitives.andCycleContract
  | .combine => Primitives.orCycleContract

@[reducible] noncomputable def certifiedChildren :
    (child : instancePorts.Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child)
  | .invertSelect =>
      ⟨.primitive Primitives.not, Primitives.notCertified.certification⟩
  | .chooseFalse | .chooseTrue =>
      ⟨.primitive Primitives.and, Primitives.andCertified.certification⟩
  | .combine =>
      ⟨.primitive Primitives.or, Primitives.orCertified.certification⟩

@[reducible] def structuralChildren :
    (child : instancePorts.Name) → ModuleStructure (instancePorts.ports child)
  | .invertSelect => .primitive Primitives.not
  | .chooseFalse | .chooseTrue => .primitive Primitives.and
  | .combine => .primitive Primitives.or

@[reducible] def childStructure := structuralChildren

def moduleStructure : ModuleStructure Modules.BitMux.ports :=
  .composite body structuralChildren

end Silean.Modules.BitMux

namespace Silean.Modules.BitMux.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming Modules.BitMux.ports where
  inputs := ⟨fun
    | .select => "select"
    | .whenFalse => "when_false"
    | .whenTrue => "when_true"⟩
  outputs := ⟨fun | .result => "result"⟩

def instanceName : Modules.BitMux.Instance → SourceName
  | .invertSelect => "invert_select"
  | .chooseFalse => "choose_false"
  | .chooseTrue => "choose_true"
  | .combine => "combine"

def childNaming : (child : Modules.BitMux.Instance) →
    ModuleNaming (Modules.BitMux.childStructure child)
  | .invertSelect => Silean.Naming.Primitive.not
  | .chooseFalse | .chooseTrue => Silean.Naming.Primitive.and
  | .combine => Silean.Naming.Primitive.or

def naming : ModuleNaming Modules.BitMux.moduleStructure := by
  unfold Modules.BitMux.moduleStructure
  exact .composite ⟨"mux", "bit_gates", []⟩ ports instanceName childNaming

end Silean.Modules.BitMux.Naming

namespace Silean.Modules.BitMux

open Silean
open Contracts.Cycle.Certification.Layer

inductive Rule
  | select
deriving Enumeration

def selectRule : Contracts.Cycle.CycleOutputRule Modules.BitMux.ports emptySignalMap
    (.ofLists [.bit, .bit, .bit] [.bit]) where
  readsInputs := ((Modules.BitMux.inputMap.select .whenTrue).prepend .whenFalse).prepend .select
  writesOutputs := Modules.BitMux.outputMap.select .result
  target
    | (select, (whenFalse, (whenTrue, ()))), _ =>
        (bif select then whenTrue else whenFalse, ())

def stateRule : Contracts.Cycle.CycleStateRule Modules.BitMux.ports emptySignalMap :=
  Contracts.Cycle.CycleStateRule.empty Modules.BitMux.ports

def cycleContract : Contracts.Cycle.ModuleCycleContract Modules.BitMux.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .select => ⟨_, selectRule⟩
  stateRule := stateRule
  outputCoverage := by rfl

abbrev invertRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.invertSelect, Primitives.NotRule.apply⟩

abbrev falseRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.chooseFalse, Primitives.AndRule.apply⟩

abbrev trueRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.chooseTrue, Primitives.AndRule.apply⟩

abbrev combineRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.combine, Primitives.OrRule.apply⟩

private def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    body childContracts cycleContract where
  output | .select => [invertRule, falseRule, trueRule, combineRule]
  state := []

private def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules
private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

theorem selectRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    selectRule.Holds inputs state outputs ↔
      outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, selectRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

section LayerCertification

variable (layerChildren : (child : instancePorts.Name) →
  Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure layerChildren) cycleContract
    (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton (child : Instance) :
      Subsingleton
        ((childContracts child).state.Values) := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have invertEvaluates := (childMatch .invertSelect).1
  have falseEvaluates := (childMatch .chooseFalse).1
  have trueEvaluates := (childMatch .chooseTrue).1
  have combineEvaluates := (childMatch .combine).1
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change selectRule.Holds inputs contractState _
    rcases proposal with ⟨outputs, children⟩
    have boundary' : outputs .result = (children .combine).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        instancePorts, EndpointContext.instanceOutput, SignalSource.value] using
          boundary Output.result
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (falseEvaluates.1 Primitives.AndRule.apply)
    have trueBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (trueEvaluates.1 Primitives.AndRule.apply)
    have combineBit := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (combineEvaluates.1 Primitives.OrRule.apply)
    change (children .invertSelect).outputs .output = !inputs .select at invertBit
    change (children .chooseFalse).outputs .output =
      (inputs .whenFalse && (children .invertSelect).outputs .output) at falseBit
    change (children .chooseTrue).outputs .output =
      (inputs .whenTrue && inputs .select) at trueBit
    change (children .combine).outputs .output =
      ((children .chooseFalse).outputs .output ||
        (children .chooseTrue).outputs .output) at combineBit
    rw [selectRule_holds_iff]
    simp only [ProposedValues.outputs]
    rw [boundary', combineBit, falseBit, trueBit, invertBit]
    cases inputs .select <;> cases inputs .whenFalse <;>
      cases inputs .whenTrue <;> rfl
  · simp [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.empty,
      Contracts.Cycle.CycleStateRule.apply, SignalSelection.project]

end LayerCertification

/-- The gate-level mux wiring implements its contract for any child
implementations satisfying the required primitive contracts. -/
noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) implements

noncomputable def certifiedStructure :
    Contracts.Cycle.ModuleCycleCertifiedStructure cycleContract :=
  certifiedLayer.instantiate certifiedChildren

@[simp] theorem certifiedStructure_moduleStructure :
    certifiedStructure.moduleStructure = moduleStructure := by
  unfold certifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    moduleStructure
  change ModuleStructure.composite body (fun child =>
    (certifiedChildren child).moduleStructure) =
      ModuleStructure.composite body structuralChildren
  congr
  funext child
  cases child <;> rfl

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedStructure.certification.transportStructure
    certifiedStructure_moduleStructure

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other →
        other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Modules.BitMux
