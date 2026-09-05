import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.SignalAdapterNaming
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Modules.VectorSplit

open Silean
open Contracts.Cycle.Certification.Layer

/-! Splits a vector into a low-index left vector and the remaining right
vector. -/

inductive Input | value
deriving Enumeration

inductive Output | left | right
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector (leftWidth + rightWidth) element

@[reducible] def outputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Output fun
    | .left => .vector leftWidth element
    | .right => .vector rightWidth element

@[reducible] def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePorts := ⟨inputMap element leftWidth rightWidth,
      outputMap element leftWidth rightWidth⟩

def leftPart (value : Fin (leftWidth + rightWidth) → α) : Fin leftWidth → α :=
  fun index => value (Fin.castAdd rightWidth index)

def rightPart (value : Fin (leftWidth + rightWidth) → α) : Fin rightWidth → α :=
  fun index => value (Fin.natAdd leftWidth index)

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.CycleOutputRule
      (ports element leftWidth rightWidth) emptySignalMap where
  readsInputs := .all (inputMap element leftWidth rightWidth)
  writesOutputs := .all (outputMap element leftWidth rightWidth)
  target inputs _ := fun
    | .left => leftPart (inputs .value)
    | .right => rightPart (inputs .value)

@[reducible] def cycleContract (element : SignalType)
    (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element leftWidth rightWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule element leftWidth rightWidth
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values) :
    (outputRule element leftWidth rightWidth).Holds inputs state outputs ↔
      outputs .left = leftPart (inputs .value) ∧
      outputs .right = rightPart (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact ⟨congrFun equal .left, congrFun equal .right⟩
  · rintro ⟨left, right⟩
    funext output
    cases output <;> assumption

theorem left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .left = leftPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.1

theorem right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .right = rightPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.2

private def splitter (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalSplitter := .vector (leftWidth + rightWidth) element

private def leftCombiner (element : SignalType) (leftWidth : Nat) :
    Composition.SignalCombiner := .vector leftWidth element

private def rightCombiner (element : SignalType) (rightWidth : Nat) :
    Composition.SignalCombiner := .vector rightWidth element

/-! ## Hardware structure -/

inductive Instance
  /-- Exposes every element of the input vector. -/
  | split
  /-- Collects the low-index elements into the left output. -/
  | left
  /-- Collects the remaining elements into the right output. -/
  | right
deriving Enumeration

@[reducible] def instancePorts (element : SignalType) (leftWidth rightWidth : Nat) :
    InstancePorts := EnumeratedMap.of Instance fun
  | .split => (splitter element leftWidth rightWidth).ports
  | .left => (leftCombiner element leftWidth).ports
  | .right => (rightCombiner element rightWidth).ports

@[reducible] def context (element : SignalType) (leftWidth rightWidth : Nat) :
    EndpointContext where
  ports := ports element leftWidth rightWidth
  instancePorts := instancePorts element leftWidth rightWidth

def wiring (element : SignalType) (leftWidth rightWidth : Nat) :
    Wiring (context element leftWidth rightWidth).ports
      (context element leftWidth rightWidth).instancePorts :=
  let c := context element leftWidth rightWidth
  { moduleOutput := fun
    -- Each combiner directly drives its corresponding output vector.
    | .left => c.instanceOutput .left .value
    | .right => c.instanceOutput .right .value
    instanceInput := fun
    -- Split the input, then route the two index ranges to their combiners.
    | .split, .value => c.moduleInput .value
    | .left, index => c.instanceOutput
        .split (Fin.castAdd rightWidth index)
    | .right, index => c.instanceOutput
        .split (Fin.natAdd leftWidth index) }

@[reducible] def body (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleBody := ⟨context element leftWidth rightWidth,
      wiring element leftWidth rightWidth⟩

@[reducible] def childContracts (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (body element leftWidth rightWidth)
  | .split => (splitter element leftWidth rightWidth).cycleContract
  | .left => (leftCombiner element leftWidth).cycleContract
  | .right => (rightCombiner element rightWidth).cycleContract

@[reducible] def structuralChildren (element : SignalType) (leftWidth rightWidth : Nat) :
    (child : Instance) → ModuleStructure ((instancePorts element leftWidth rightWidth).ports child)
  | .split => .splitter (splitter element leftWidth rightWidth)
  | .left => .combiner (leftCombiner element leftWidth)
  | .right => .combiner (rightCombiner element rightWidth)

@[reducible] noncomputable def certifiedChildren
    (element : SignalType) (leftWidth rightWidth : Nat) :
    (child : Instance) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (childContracts element leftWidth rightWidth child)
  | .split => ⟨.splitter (splitter element leftWidth rightWidth),
      (splitter element leftWidth rightWidth).certified.certification⟩
  | .left => ⟨.combiner (leftCombiner element leftWidth),
      (leftCombiner element leftWidth).certified.certification⟩
  | .right => ⟨.combiner (rightCombiner element rightWidth),
      (rightCombiner element rightWidth).certified.certification⟩

def moduleStructure (element : SignalType) (leftWidth rightWidth : Nat) :
  ModuleStructure (ports element leftWidth rightWidth) :=
  .composite (body element leftWidth rightWidth)
    (structuralChildren element leftWidth rightWidth)

private abbrev splitOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩

private abbrev leftOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.left, Composition.SignalComponentRule.apply⟩

private abbrev rightOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.right, Composition.SignalComponentRule.apply⟩

private def scheduleOrders (element : SignalType) (leftWidth rightWidth : Nat) :
    ScheduleDerivation.RuleScheduleOrders (body element leftWidth rightWidth)
      (childContracts element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) where
  output | .apply => [splitOccurrence element leftWidth rightWidth,
    leftOccurrence element leftWidth rightWidth,
    rightOccurrence element leftWidth rightWidth]
  state := []

private def derivedRuleSchedules (element : SignalType) (leftWidth rightWidth : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (body element leftWidth rightWidth)
      (childContracts element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) := by
  derive_rule_schedules (scheduleOrders element leftWidth rightWidth)

private abbrev ruleSchedules (element : SignalType) (leftWidth rightWidth : Nat) :=
  (derivedRuleSchedules element leftWidth rightWidth).schedules

private theorem coversChildren (element : SignalType) (leftWidth rightWidth : Nat) :
    (ruleSchedules element leftWidth rightWidth).CoversChildren :=
  (derivedRuleSchedules element leftWidth rightWidth).coversChildren

def splitInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (splitter element leftWidth rightWidth).ports.inputs.Values
  | .value => inputs .value

section LayerCertification

variable (element : SignalType) (leftWidth rightWidth : Nat)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element leftWidth rightWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body element leftWidth rightWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element leftWidth rightWidth layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (certificationStructure element leftWidth rightWidth layerChildren)
      (cycleContract element leftWidth rightWidth)
      (stateCorresponds element leftWidth rightWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have boundary := satisfies.1
  have childMatch (child : Instance) := by
    letI : Subsingleton
        ((childContracts element leftWidth rightWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs
        structuralState (ProposedValues.composite outputs proposals) satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
  have splitOutputs : (proposals .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (splitInputs element leftWidth rightWidth inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element leftWidth rightWidth) _ _ _).mp
      ((childMatch .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth)
        ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .split = splitInputs element leftWidth rightWidth inputs := by
      funext input; cases input; rfl
    change (proposals .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth)
          ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .split) at holds
    rw [inputsEqual] at holds
    exact holds
  have leftOutputs : (proposals .left).outputs =
      (leftCombiner element leftWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .left) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .left).1.1 Composition.SignalComponentRule.apply)
  have rightOutputs : (proposals .right).outputs =
      (rightCombiner element rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .right) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .right).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change outputs .left = leftPart (inputs .value)
      rw [show outputs .left = (proposals .left).outputs .value by
        exact boundary .left]
      rw [congrFun leftOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.castAdd rightWidth index) =
        inputs .value (Fin.castAdd rightWidth index)
      rw [splitOutputs]
      rfl
    · change outputs .right = rightPart (inputs .value)
      rw [show outputs .right = (proposals .right).outputs .value by
        exact boundary .right]
      rw [congrFun rightOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.natAdd leftWidth index) =
        inputs .value (Fin.natAdd leftWidth index)
      rw [splitOutputs]
      rfl
  · rfl

end LayerCertification

noncomputable opaque certifiedLayer (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body element leftWidth rightWidth)
      (childContracts element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules element leftWidth rightWidth)
    (coversChildren element leftWidth rightWidth)
    (stateCorresponds element leftWidth rightWidth)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (implements element leftWidth rightWidth)

noncomputable def certification (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) :=
  (certifiedLayer element leftWidth rightWidth).certifyComposite
    (structuralChildren element leftWidth rightWidth)
    (certifiedChildren element leftWidth rightWidth)
    (by intro child; cases child <;> rfl)

  noncomputable def certified (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports element leftWidth rightWidth) :=
  (certification element leftWidth rightWidth).bundle

end Silean.Modules.VectorSplit

namespace Silean.Modules.VectorSplit.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.VectorSplit.ports element leftWidth rightWidth) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .left => "left" | .right => "right"⟩
  inputTypes := fun | .value => .vector elementNaming
  outputTypes := fun | .left | .right => .vector elementNaming

def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePortsNaming (Modules.VectorSplit.ports element leftWidth rightWidth) :=
  portsWithNaming element leftWidth rightWidth (.positional element)

def namingWith (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.VectorSplit.moduleStructure element leftWidth rightWidth) :=
  .composite
    ⟨"vector_split", "structural",
      [.signalType element, .natural leftWidth, .natural rightWidth]⟩
    (portsWithNaming element leftWidth rightWidth elementNaming)
    (fun | .split => "split" | .left => "combine_left" | .right => "combine_right")
    (fun
      | .split => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector (leftWidth + rightWidth) element) (.vector elementNaming)
      | .left => Silean.Naming.SignalAdapter.combinerWithNaming
          (.vector leftWidth element) (.vector elementNaming)
      | .right => Silean.Naming.SignalAdapter.combinerWithNaming
          (.vector rightWidth element) (.vector elementNaming))

def naming (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleNaming (Modules.VectorSplit.moduleStructure element leftWidth rightWidth) :=
  namingWith element leftWidth rightWidth (.positional element)

def namedModule (element : SignalType) (leftWidth rightWidth : Nat) : NamedModule where
  ports := Modules.VectorSplit.ports element leftWidth rightWidth
  moduleStructure := Modules.VectorSplit.moduleStructure element leftWidth rightWidth
  naming := naming element leftWidth rightWidth

end Silean.Modules.VectorSplit.Naming
