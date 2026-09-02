import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.SignalAdapterNaming
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Modules.VectorSlice

open Silean
open Contracts.Cycle.Certification.Layer

/-! Extracts a contiguous vector range. `prefixWidth` elements precede the
result and `suffixWidth` elements follow it, so the source width is
`prefixWidth + width + suffixWidth`. -/

inductive Input | value
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector (prefixWidth + width + suffixWidth) element

@[reducible] def outputMap (element : SignalType) (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .result => .vector width element

@[reducible] def ports (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : ModulePorts :=
  ⟨inputMap element prefixWidth width suffixWidth, outputMap element width⟩

def slice (value : Fin (prefixWidth + width + suffixWidth) → α) :
    Fin width → α :=
  fun index => value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index))

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.CycleOutputRule
      (ports element prefixWidth width suffixWidth) emptySignalMap
      { inputTypes := .cons (.vector (prefixWidth + width + suffixWidth) element) .nil
        outputTypes := .cons (.vector width element) .nil } where
  readsInputs := (inputMap element prefixWidth width suffixWidth).select .value
  writesOutputs := (outputMap element width).select .result
  target | (value, ()), _ => (slice value, ())

@[reducible] def cycleContract (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract
      (ports element prefixWidth width suffixWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule element prefixWidth width suffixWidth⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (inputs : (ports element prefixWidth width suffixWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element prefixWidth width suffixWidth).outputs.Values) :
    (outputRule element prefixWidth width suffixWidth).Holds inputs state outputs ↔
      outputs .result = slice (inputs .value) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

theorem result_at_of_holds (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (inputs : (ports element prefixWidth width suffixWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element prefixWidth width suffixWidth).outputs.Values)
    (holds : (outputRule element prefixWidth width suffixWidth).Holds inputs state outputs)
    (index : Fin width) :
    outputs .result index =
      inputs .value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) := by
  rw [(outputRule_holds_iff element prefixWidth width suffixWidth
    inputs state outputs).mp holds]
  rfl

private def splitter (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : Composition.SignalSplitter :=
  .vector (prefixWidth + width + suffixWidth) element

private def combiner (element : SignalType) (width : Nat) :
    Composition.SignalCombiner := .vector width element

/-! ## Hardware structure -/

inductive Instance
  /-- Exposes every source-vector element. -/
  | split
  /-- Collects the selected elements into the result vector. -/
  | combine
deriving Enumeration

@[reducible] def instancePorts (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .split => (splitter element prefixWidth width suffixWidth).ports
    | .combine => (combiner element width).ports

@[reducible] def context (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : EndpointContext where
  ports := ports element prefixWidth width suffixWidth
  instancePorts := instancePorts element prefixWidth width suffixWidth

def wiring (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    Wiring (context element prefixWidth width suffixWidth).ports
      (context element prefixWidth width suffixWidth).instancePorts :=
  let c := context element prefixWidth width suffixWidth
  { moduleOutput := fun | .result => c.instanceOutput .combine .value
    instanceInput := fun
      | .split, .value => c.moduleInput .value
      | .combine, index => c.instanceOutput .split
          (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) }

@[reducible] def body (element : SignalType)
    (prefixWidth width suffixWidth : Nat) : ModuleBody :=
  ⟨context element prefixWidth width suffixWidth,
    wiring element prefixWidth width suffixWidth⟩

@[reducible] def childContracts (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts
      (body element prefixWidth width suffixWidth)
  | .split => (splitter element prefixWidth width suffixWidth).cycleContract
  | .combine => (combiner element width).cycleContract

@[reducible] def structuralChildren (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    (child : Instance) →
      ModuleStructure ((instancePorts element prefixWidth width suffixWidth).ports child)
  | .split => .splitter (splitter element prefixWidth width suffixWidth)
  | .combine => .combiner (combiner element width)

@[reducible] noncomputable def certifiedChildren (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    (child : Instance) → Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element prefixWidth width suffixWidth child)
  | .split => ⟨.splitter (splitter element prefixWidth width suffixWidth),
      (splitter element prefixWidth width suffixWidth).certified.certification⟩
  | .combine => ⟨.combiner (combiner element width),
      (combiner element width).certified.certification⟩

def moduleStructure (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    ModuleStructure (ports element prefixWidth width suffixWidth) :=
  .composite (body element prefixWidth width suffixWidth)
    (structuralChildren element prefixWidth width suffixWidth)

private abbrev splitOccurrence (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element prefixWidth width suffixWidth)
      (childContracts element prefixWidth width suffixWidth) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩

private abbrev combineOccurrence (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element prefixWidth width suffixWidth)
      (childContracts element prefixWidth width suffixWidth) :=
  ⟨.combine, Composition.SignalComponentRule.apply⟩

private def scheduleOrders (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    ScheduleDerivation.RuleScheduleOrders
      (body element prefixWidth width suffixWidth)
      (childContracts element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth) where
  output | .apply => [splitOccurrence element prefixWidth width suffixWidth,
    combineOccurrence element prefixWidth width suffixWidth]
  state := []

private def derivedRuleSchedules (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    ScheduleDerivation.DerivedRuleSchedules
      (body element prefixWidth width suffixWidth)
      (childContracts element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth) := by
  derive_rule_schedules (scheduleOrders element prefixWidth width suffixWidth)

private abbrev ruleSchedules (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :=
  (derivedRuleSchedules element prefixWidth width suffixWidth).schedules

private theorem coversChildren (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    (ruleSchedules element prefixWidth width suffixWidth).CoversChildren :=
  (derivedRuleSchedules element prefixWidth width suffixWidth).coversChildren

section LayerCertification

variable (element : SignalType) (prefixWidth width suffixWidth : Nat)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element prefixWidth width suffixWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element prefixWidth width suffixWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element prefixWidth width suffixWidth layerChildren).State) :
    Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure element prefixWidth width suffixWidth layerChildren)
    (cycleContract element prefixWidth width suffixWidth)
    (stateCorresponds element prefixWidth width suffixWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have childMatch (child : Instance) := by
    letI : Subsingleton
        ((childContracts element prefixWidth width suffixWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState (ProposedValues.composite outputs proposals)
        satisfies child (by cases child <;> exact SignalMap.emptyValues)
  have splitOutputs : (proposals .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        (fun | .value => inputs .value) := by
    have held := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element prefixWidth width suffixWidth) _ _ _).mp
      ((childMatch .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs
        (body element prefixWidth width suffixWidth)
        (fun name => (layerChildren name).moduleStructure) inputs proposals .split =
          (fun | .value => inputs .value) := by
      funext input
      cases input
      rfl
    change (proposals .split).outputs =
      (splitter element prefixWidth width suffixWidth).outputValues
        (ProposedValues.childInputs (body element prefixWidth width suffixWidth)
          (fun name => (layerChildren name).moduleStructure) inputs proposals .split) at held
    rw [inputsEqual] at held
    exact held
  have combineOutputs : (proposals .combine).outputs =
      (combiner element width).outputValues
        (ProposedValues.childInputs (body element prefixWidth width suffixWidth)
          (fun name => (layerChildren name).moduleStructure)
          inputs proposals .combine) :=
    (Composition.SignalCombiner.outputRule_holds_iff
      (combiner element width) _ _ _).mp
      ((childMatch .combine).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = slice (inputs .value)
    rw [show outputs .result = (proposals .combine).outputs .value by
      exact satisfies.1 .result]
    rw [congrFun combineOutputs .value]
    funext index
    change (proposals .split).outputs
      (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) = _
    rw [splitOutputs]
    rfl
  · rfl

end LayerCertification

noncomputable opaque certifiedLayer (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body element prefixWidth width suffixWidth)
      (childContracts element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules element prefixWidth width suffixWidth)
    (coversChildren element prefixWidth width suffixWidth)
    (stateCorresponds element prefixWidth width suffixWidth)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (implements element prefixWidth width suffixWidth)

noncomputable def certification (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth) :=
  (certifiedLayer element prefixWidth width suffixWidth).certifyComposite
    (structuralChildren element prefixWidth width suffixWidth)
    (certifiedChildren element prefixWidth width suffixWidth)
    (by intro child; cases child <;> rfl)

noncomputable def certified (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified
      (ports element prefixWidth width suffixWidth) :=
  (certification element prefixWidth width suffixWidth).bundle

@[simp] theorem certified_moduleStructure (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    (certified element prefixWidth width suffixWidth).moduleStructure =
      moduleStructure element prefixWidth width suffixWidth := rfl

@[simp] theorem certified_cycleContract (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    (certified element prefixWidth width suffixWidth).cycleContract =
      cycleContract element prefixWidth width suffixWidth := rfl

theorem result_of_evaluatesTo (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (inputs : (ports element prefixWidth width suffixWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element prefixWidth width suffixWidth).outputs.Values)
    (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract element prefixWidth width suffixWidth).EvaluatesTo
      inputs state outputs nextState) :
    outputs .result = slice (inputs .value) :=
  (outputRule_holds_iff element prefixWidth width suffixWidth inputs state outputs).mp
    (evaluates.1 .apply)

end Silean.Modules.VectorSlice

namespace Silean.Modules.VectorSlice.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (prefixWidth width suffixWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.VectorSlice.ports element prefixWidth width suffixWidth) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => .vector elementNaming
  outputTypes := fun | .result => .vector elementNaming

def ports (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    ModulePortsNaming (Modules.VectorSlice.ports element prefixWidth width suffixWidth) :=
  portsWithNaming element prefixWidth width suffixWidth (.positional element)

def namingWith (element : SignalType) (prefixWidth width suffixWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.VectorSlice.moduleStructure
      element prefixWidth width suffixWidth) :=
  .composite
    ⟨"vector_slice", "structural",
      [.shape element, .natural prefixWidth, .natural width, .natural suffixWidth]⟩
    (portsWithNaming element prefixWidth width suffixWidth elementNaming)
    (fun | .split => "split" | .combine => "combine")
    (fun
      | .split => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector (prefixWidth + width + suffixWidth) element) (.vector elementNaming)
      | .combine => Silean.Naming.SignalAdapter.combinerWithNaming
          (.vector width element) (.vector elementNaming))

def naming (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    ModuleNaming (Modules.VectorSlice.moduleStructure
      element prefixWidth width suffixWidth) :=
  namingWith element prefixWidth width suffixWidth (.positional element)

def namedModule (element : SignalType) (prefixWidth width suffixWidth : Nat) : NamedModule where
  ports := Modules.VectorSlice.ports element prefixWidth width suffixWidth
  moduleStructure := Modules.VectorSlice.moduleStructure element prefixWidth width suffixWidth
  naming := naming element prefixWidth width suffixWidth

end Silean.Modules.VectorSlice.Naming
