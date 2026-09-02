import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.SignalAdapterNaming
import Silean.Composition.SignalAdapterImplementation

namespace Silean.Modules.VectorConcat

open Silean
open Contracts.Cycle.Certification.Layer

/-! Concatenates two vectors of the same element type, with the left vector at
the lower result indices. -/

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Input fun
    | .left => .vector leftWidth element
    | .right => .vector rightWidth element

@[reducible] def outputMap (element : SignalType) (leftWidth rightWidth : Nat) :
    SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector (leftWidth + rightWidth) element

@[reducible] def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePorts := ⟨inputMap element leftWidth rightWidth,
      outputMap element leftWidth rightWidth⟩

def concat (left : Fin leftWidth → α) (right : Fin rightWidth → α) :
    Fin (leftWidth + rightWidth) → α :=
  Fin.addCases left right

@[simp] theorem concat_left (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin leftWidth) :
    concat left right (Fin.castAdd rightWidth index) = left index := by
  simp [concat]

@[simp] theorem concat_right (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin rightWidth) :
    concat left right (Fin.natAdd leftWidth index) = right index := by
  simp [concat]

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element leftWidth rightWidth) emptySignalMap
      { inputTypes := .cons (.vector leftWidth element)
          (.cons (.vector rightWidth element) .nil)
        outputTypes := .cons (.vector (leftWidth + rightWidth) element) .nil } where
  readsInputs := ((inputMap element leftWidth rightWidth).select .right).prepend .left
  writesOutputs := (outputMap element leftWidth rightWidth).select .result
  target | (left, (right, ())), _ => (concat left right, ())

@[reducible] def cycleContract (element : SignalType)
    (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element leftWidth rightWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule element leftWidth rightWidth⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values) :
    (outputRule element leftWidth rightWidth).Holds inputs state outputs ↔
      outputs .result = concat (inputs .left) (inputs .right) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem result_left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin leftWidth) :
    outputs .result (Fin.castAdd rightWidth index) = inputs .left index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_left _ _ index

theorem result_right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin rightWidth) :
    outputs .result (Fin.natAdd leftWidth index) = inputs .right index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_right _ _ index

private def leftSplitter (element : SignalType) (leftWidth : Nat) : Composition.SignalSplitter :=
  .vector leftWidth element

private def rightSplitter (element : SignalType) (rightWidth : Nat) : Composition.SignalSplitter :=
  .vector rightWidth element

private def combiner (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalCombiner := .vector (leftWidth + rightWidth) element

/-! ## Hardware structure -/

inductive Instance
  /-- Exposes the elements of the left input vector. -/
  | leftSplit
  /-- Exposes the elements of the right input vector. -/
  | rightSplit
  /-- Collects both sets of elements into the result vector. -/
  | combine
deriving Enumeration

@[reducible] def instancePorts (element : SignalType) (leftWidth rightWidth : Nat) :
    InstancePorts := EnumeratedMap.of Instance fun
  | .leftSplit => (leftSplitter element leftWidth).ports
  | .rightSplit => (rightSplitter element rightWidth).ports
  | .combine => (combiner element leftWidth rightWidth).ports

@[reducible] def context (element : SignalType) (leftWidth rightWidth : Nat) :
    EndpointContext where
  ports := ports element leftWidth rightWidth
  instancePorts := instancePorts element leftWidth rightWidth

def wiring (element : SignalType) (leftWidth rightWidth : Nat) :
    Wiring (context element leftWidth rightWidth).ports
      (context element leftWidth rightWidth).instancePorts :=
  let c := context element leftWidth rightWidth
  { moduleOutput := fun
    -- The combiner produces the concatenated vector.
    | .result => c.instanceOutput .combine .value
    instanceInput := fun
    -- Split both input vectors into elements.
    | .leftSplit, .value =>
        c.moduleInput .left
    | .rightSplit, .value =>
        c.moduleInput .right
    -- Feed left elements first, followed by right elements.
    | .combine, index =>
        Fin.addCases
          (fun leftIndex =>
            c.instanceOutput
              .leftSplit leftIndex)
          (fun rightIndex =>
            c.instanceOutput
              .rightSplit rightIndex)
          index }

@[reducible] def body (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleBody := ⟨context element leftWidth rightWidth,
      wiring element leftWidth rightWidth⟩

@[reducible] def childContracts (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (body element leftWidth rightWidth)
  | .leftSplit => (leftSplitter element leftWidth).cycleContract
  | .rightSplit => (rightSplitter element rightWidth).cycleContract
  | .combine => (combiner element leftWidth rightWidth).cycleContract

@[reducible] def structuralChildren (element : SignalType) (leftWidth rightWidth : Nat) :
    (child : Instance) → ModuleStructure ((instancePorts element leftWidth rightWidth).ports child)
  | .leftSplit => .splitter (leftSplitter element leftWidth)
  | .rightSplit => .splitter (rightSplitter element rightWidth)
  | .combine => .combiner (combiner element leftWidth rightWidth)

@[reducible] noncomputable def certifiedChildren
    (element : SignalType) (leftWidth rightWidth : Nat) :
    (child : Instance) → Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element leftWidth rightWidth child)
  | .leftSplit => ⟨.splitter (leftSplitter element leftWidth),
      (leftSplitter element leftWidth).certified.certification⟩
  | .rightSplit => ⟨.splitter (rightSplitter element rightWidth),
      (rightSplitter element rightWidth).certified.certification⟩
  | .combine => ⟨.combiner (combiner element leftWidth rightWidth),
      (combiner element leftWidth rightWidth).certified.certification⟩

def moduleStructure (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleStructure (ports element leftWidth rightWidth) :=
  .composite (body element leftWidth rightWidth)
    (structuralChildren element leftWidth rightWidth)

abbrev leftOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.leftSplit, Composition.SignalComponentRule.apply⟩

abbrev rightOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.rightSplit, Composition.SignalComponentRule.apply⟩

abbrev combineOccurrence (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body element leftWidth rightWidth) (childContracts element leftWidth rightWidth) :=
  ⟨.combine, Composition.SignalComponentRule.apply⟩

private def scheduleOrders (element : SignalType)
    (leftWidth rightWidth : Nat) : ScheduleDerivation.RuleScheduleOrders
      (body element leftWidth rightWidth)
      (childContracts element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth) where
  output | .apply => [leftOccurrence element leftWidth rightWidth,
    rightOccurrence element leftWidth rightWidth,
    combineOccurrence element leftWidth rightWidth]
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

def leftInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (leftSplitter element leftWidth).ports.inputs.Values
  | .value => inputs .left

def rightInputs (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (rightSplitter element rightWidth).ports.inputs.Values
  | .value => inputs .right

def combineInputs
    (left : (leftSplitter element leftWidth).ports.outputs.Values)
    (right : (rightSplitter element rightWidth).ports.outputs.Values) :
    (combiner element leftWidth rightWidth).ports.inputs.Values := fun index =>
  Fin.addCases (fun leftIndex => left leftIndex)
    (fun rightIndex => right rightIndex) index

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
  have leftOutputs : (proposals .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues (leftInputs inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (leftSplitter element leftWidth) _ _ _).mp
      ((childMatch .leftSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth)
        ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .leftSplit = leftInputs inputs := by funext input; cases input; rfl
    change (proposals .leftSplit).outputs =
      (leftSplitter element leftWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth)
          ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .leftSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have rightOutputs : (proposals .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues (rightInputs inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (rightSplitter element rightWidth) _ _ _).mp
      ((childMatch .rightSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth)
        ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .rightSplit = rightInputs inputs := by funext input; cases input; rfl
    change (proposals .rightSplit).outputs =
      (rightSplitter element rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth)
          ((fun name => (layerChildren name).moduleStructure)) inputs proposals
          .rightSplit) at holds
    rw [inputsEqual] at holds
    exact holds
  have combineOutputs : (proposals .combine).outputs =
      (combiner element leftWidth rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .combine) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .combine).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = concat (inputs .left) (inputs .right)
    rw [show outputs .result = (proposals .combine).outputs .value by
      exact boundary .result]
    rw [congrFun combineOutputs .value]
    rw [show ProposedValues.childInputs (body element leftWidth rightWidth) _
        inputs proposals .combine =
          combineInputs (proposals .leftSplit).outputs
            (proposals .rightSplit).outputs by
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro leftIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]
      · intro rightIndex
        simp [ProposedValues.childInputs, body, wiring, combineInputs,
          EndpointContext.instanceOutput, SignalSource.value]]
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro leftIndex
      simp [combiner, Composition.SignalCombiner.outputValues, combineInputs, concat]
      rw [leftOutputs]
      rfl
    · intro rightIndex
      simp [combiner, Composition.SignalCombiner.outputValues, combineInputs, concat]
      rw [rightOutputs]
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

end Silean.Modules.VectorConcat

namespace Silean.Modules.VectorConcat.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.VectorConcat.ports element leftWidth rightWidth) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .left => .vector elementNaming
    | .right => .vector elementNaming
  outputTypes := fun | .result => .vector elementNaming

def ports (element : SignalType) (leftWidth rightWidth : Nat) :
    ModulePortsNaming (Modules.VectorConcat.ports element leftWidth rightWidth) :=
  portsWithNaming element leftWidth rightWidth (.positional element)

def namingWith (element : SignalType) (leftWidth rightWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.VectorConcat.moduleStructure element leftWidth rightWidth) :=
  .composite
    ⟨"vector_concat", "structural",
      [.shape element, .natural leftWidth, .natural rightWidth]⟩
    (portsWithNaming element leftWidth rightWidth elementNaming)
    (fun
      | .leftSplit => "split_left"
      | .rightSplit => "split_right"
      | .combine => "combine")
    (fun
      | .leftSplit => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector leftWidth element) (.vector elementNaming)
      | .rightSplit => Silean.Naming.SignalAdapter.splitterWithNaming
          (.vector rightWidth element) (.vector elementNaming)
      | .combine => Silean.Naming.SignalAdapter.combinerWithNaming
          (.vector (leftWidth + rightWidth) element) (.vector elementNaming))

def naming (element : SignalType) (leftWidth rightWidth : Nat) :
    ModuleNaming (Modules.VectorConcat.moduleStructure element leftWidth rightWidth) :=
  namingWith element leftWidth rightWidth (.positional element)

def namedModule (element : SignalType) (leftWidth rightWidth : Nat) : NamedModule where
  ports := Modules.VectorConcat.ports element leftWidth rightWidth
  moduleStructure := Modules.VectorConcat.moduleStructure element leftWidth rightWidth
  naming := naming element leftWidth rightWidth

end Silean.Modules.VectorConcat.Naming
