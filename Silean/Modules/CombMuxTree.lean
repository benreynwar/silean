import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.BinaryToOneHot
import Silean.Modules.Mux
import Silean.Modules.VectorSplit
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.CombMuxTree

open Silean
open Contracts.Cycle.Certification.Layer

/-! A combinational mux tree selecting one of `2 ^ indexWidth` values. -/

inductive Input | values | index
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (element : SignalType) (indexWidth : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .values => .vector (BinaryToOneHot.size indexWidth) element
    | .index => .vector indexWidth .bit

@[reducible] def outputMap (element : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .result => element

@[reducible] def ports (element : SignalType) (indexWidth : Nat) : ModulePorts :=
  ⟨inputMap element indexWidth, outputMap element⟩

def select (indexWidth : Nat) (values : Fin (BinaryToOneHot.size indexWidth) → α)
    (bits : Fin indexWidth → Bool) : α :=
  values (BitVector.toIndex indexWidth bits)

inductive Rule | apply
deriving Enumeration

def outputRule (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element indexWidth) emptySignalMap
      { inputTypes := .cons (.vector (BinaryToOneHot.size indexWidth) element)
          (.cons (.vector indexWidth .bit) .nil)
        outputTypes := .cons element .nil } where
  readsInputs := ((inputMap element indexWidth).select .index).prepend .values
  writesOutputs := (outputMap element).select .result
  target | (values, (index, ())), _ => (select indexWidth values index, ())

@[reducible] def cycleContract (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports element indexWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule element indexWidth⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element indexWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element indexWidth).outputs.Values) :
    (outputRule element indexWidth).Holds inputs state outputs ↔
      outputs .result = select indexWidth (inputs .values) (inputs .index) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

theorem result_of_holds (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element indexWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element indexWidth).outputs.Values)
    (holds : (outputRule element indexWidth).Holds inputs state outputs) :
    outputs .result = inputs .values
      ⟨BitVector.toNat indexWidth (inputs .index),
        BitVector.toNat_lt_cardinality indexWidth (inputs .index)⟩ := by
  rw [(outputRule_holds_iff element indexWidth inputs state outputs).mp holds]
  unfold select
  apply congrArg (inputs .values)
  apply Fin.ext
  exact BitVector.toIndex_val indexWidth (inputs .index)

/-! ## Hardware structure

Width zero has one value and no selector bits. -/

private def baseSplitter (element : SignalType) : Composition.SignalSplitter := .vector 1 element

private inductive BaseInstance
  /-- Exposes the sole input value. -/
  | split
deriving Enumeration

@[reducible] private def baseInstances (element : SignalType) : InstancePorts :=
  EnumeratedMap.of BaseInstance fun | .split => (baseSplitter element).ports

@[reducible] private def baseContext (element : SignalType) : EndpointContext where
  ports := ports element 0
  instancePorts := baseInstances element

private def baseWiring (element : SignalType) :
    Wiring (baseContext element).ports (baseContext element).instancePorts where
  moduleOutput | .result => baseContext element |>.instanceOutput .split ⟨0, by omega⟩
  instanceInput | .split, .value => baseContext element |>.moduleInput .values

@[reducible] private def baseBody (element : SignalType) : ModuleBody :=
  ⟨baseContext element, baseWiring element⟩

private def baseModuleStructure (element : SignalType) :
    ModuleStructure (ports element 0) :=
  .composite (baseBody element) fun
    | .split => (baseSplitter element).certified.moduleStructure

/-! A successor width partitions values into equal halves and the index into
lower bits/high bit, selects recursively from both halves, then chooses with
`Mux`. -/

private def indexSplitter (indexWidth : Nat) : Composition.SignalSplitter :=
  .vector (indexWidth + 1) .bit
private def indexLowerCombiner (indexWidth : Nat) : Composition.SignalCombiner :=
  .vector indexWidth .bit
private def highIndex (indexWidth : Nat) : (indexSplitter indexWidth).ports.outputs.Label :=
  Fin.last indexWidth

inductive SuccInstance
  /-- Divides the candidate values into lower and upper halves. -/
  | valuesSplit
  /-- Exposes the selector bits. -/
  | indexSplit
  /-- Rebuilds the lower selector bits for recursive selection. -/
  | indexLower
  /-- Selects recursively from the lower half. -/
  | lower
  /-- Selects recursively from the upper half. -/
  | upper
  /-- Uses the high selector bit to choose between the halves. -/
  | mux
deriving Enumeration

@[reducible] def succInstances (element : SignalType) (indexWidth : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .valuesSplit => VectorSplit.ports element
        (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    | .indexSplit => (indexSplitter indexWidth).ports
    | .indexLower => (indexLowerCombiner indexWidth).ports
    | .lower | .upper => ports element indexWidth
    | .mux => Mux.ports element

@[reducible] def succContext (element : SignalType) (indexWidth : Nat) :
    EndpointContext where
  ports := ports element (indexWidth + 1)
  instancePorts := succInstances element indexWidth

def succWiring (element : SignalType) (indexWidth : Nat) :
    Wiring (succContext element indexWidth).ports
      (succContext element indexWidth).instancePorts where
  moduleOutput | .result => (succContext element indexWidth).instanceOutput .mux .result
  instanceInput
    -- Split the candidates and selector.
    | .valuesSplit, .value =>
        (succContext element indexWidth).moduleInput .values
    | .indexSplit, .value =>
        (succContext element indexWidth).moduleInput .index
    | .indexLower, lowerIndex =>
        (succContext element indexWidth).instanceOutput .indexSplit lowerIndex.castSucc
    -- Both recursive muxes use the same lower selector bits.
    | .lower, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .left
    | .lower, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
    | .upper, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .right
    | .upper, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
    -- The high selector bit chooses the recursive result.
    | .mux, .select =>
        (succContext element indexWidth).instanceOutput .indexSplit (highIndex indexWidth)
    | .mux, .whenFalse =>
        (succContext element indexWidth).instanceOutput .lower .result
    | .mux, .whenTrue =>
        (succContext element indexWidth).instanceOutput .upper .result

@[reducible] def succBody (element : SignalType) (indexWidth : Nat) : ModuleBody :=
  ⟨succContext element indexWidth, succWiring element indexWidth⟩

def moduleStructure (element : SignalType) : (indexWidth : Nat) →
    ModuleStructure (ports element indexWidth)
  | 0 => baseModuleStructure element
  | indexWidth + 1 => .composite (succBody element indexWidth) fun
      | .valuesSplit => VectorSplit.moduleStructure element
          (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
      | .indexSplit => (indexSplitter indexWidth).certified.moduleStructure
      | .indexLower => (indexLowerCombiner indexWidth).certified.moduleStructure
      | .lower | .upper => moduleStructure element indexWidth
      | .mux => Mux.moduleStructure element

private abbrev Implementation (element : SignalType) (indexWidth : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure element indexWidth)
    (cycleContract element indexWidth)

private def Implementation.certified
    (implementation : Implementation element indexWidth) :
    Contracts.Cycle.ModuleCycleCertified (ports element indexWidth) := implementation.bundle

@[reducible] private def baseChildContracts (element : SignalType) :
    Contracts.Cycle.ChildCycleContracts (baseBody element)
  | .split => (baseSplitter element).cycleContract

private abbrev baseOccurrence (element : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (baseBody element) (baseChildContracts element) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩

private def baseScheduleOrders (element : SignalType) :
    ScheduleDerivation.RuleScheduleOrders (baseBody element)
      (baseChildContracts element) (cycleContract element 0) where
  output | .apply => [baseOccurrence element]
  state := []

private def baseDerivedRuleSchedules (element : SignalType) :
    ScheduleDerivation.DerivedRuleSchedules (baseBody element)
      (baseChildContracts element) (cycleContract element 0) := by
  derive_rule_schedules (baseScheduleOrders element)

private abbrev baseSchedules (element : SignalType) :=
  (baseDerivedRuleSchedules element).schedules

private theorem baseCoversChildren (element : SignalType) :
    (baseSchedules element).CoversChildren :=
  (baseDerivedRuleSchedules element).coversChildren

private def baseSplitInputs (element : SignalType)
    (inputs : (ports element 0).inputs.Values) :
    (baseSplitter element).ports.inputs.Values
  | .value => inputs .values

private theorem baseImplements (element : SignalType)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (baseBody element) (baseChildContracts element)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure (baseBody element) layerChildren)
      (cycleContract element 0)
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  have boundary := satisfies.1
  have splitOutputs : (children .split).outputs =
      (baseSplitter element).outputValues (baseSplitInputs element inputs) := by
    have stateSubsingleton :
        Subsingleton (baseChildContracts element .split).state.Values := by
      change Subsingleton emptySignalMap.Values
      infer_instance
    have evaluates :=
      letI := stateSubsingleton
      (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
        layerChildren inputs structuralState ⟨outputs, children⟩ satisfies
        .split SignalMap.emptyValues).1
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (baseSplitter element) _ _ _).mp
      (evaluates.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (baseBody element)
        (fun child => (layerChildren child).moduleStructure) inputs children .split =
        baseSplitInputs element inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = _
    rw [show outputs .result = (children .split).outputs ⟨0, by omega⟩ by
      exact boundary .result]
    rw [congrFun splitOutputs ⟨0, by omega⟩]
    rfl
  · rfl

private noncomputable opaque baseCertifiedLayer (element : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (baseBody element)
      (baseChildContracts element) (cycleContract element 0) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (baseSchedules element) (baseCoversChildren element) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (baseImplements element)

private noncomputable def baseCertifiedChildren (element : SignalType) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (baseBody element) (baseChildContracts element)
  | .split => (baseSplitter element).certified.certifiedStructure

private noncomputable def baseImplementation (element : SignalType) : Implementation element 0 :=
  ((baseCertifiedLayer element).certify (baseCertifiedChildren element)).transportStructure (by rfl)

@[reducible] private def succChildContracts (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody element indexWidth)
  | .valuesSplit => VectorSplit.cycleContract element
      (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
  | .indexSplit => (indexSplitter indexWidth).cycleContract
  | .indexLower => (indexLowerCombiner indexWidth).cycleContract
  | .lower | .upper => cycleContract element indexWidth
  | .mux => Mux.cycleContract element

private abbrev valuesSplitOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.valuesSplit, VectorSplit.Rule.apply⟩
private abbrev indexSplitOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.indexSplit, Composition.SignalComponentRule.apply⟩
private abbrev indexLowerOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.indexLower, Composition.SignalComponentRule.apply⟩
private abbrev lowerOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.lower, Rule.apply⟩
private abbrev upperOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.upper, Rule.apply⟩
private abbrev muxOccurrence (element) (indexWidth) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.mux, Mux.Rule.select⟩

private def succScheduleOrders (element : SignalType) (indexWidth : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody element indexWidth)
      (succChildContracts element indexWidth)
      (cycleContract element (indexWidth + 1)) where
  output := fun
    | .apply => [valuesSplitOccurrence element indexWidth,
        indexSplitOccurrence element indexWidth,
        indexLowerOccurrence element indexWidth,
        lowerOccurrence element indexWidth, upperOccurrence element indexWidth,
        muxOccurrence element indexWidth]
  state := []

private def succDerivedRuleSchedules (element : SignalType) (indexWidth : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (succBody element indexWidth)
      (succChildContracts element indexWidth)
      (cycleContract element (indexWidth + 1)) := by
  derive_rule_schedules (succScheduleOrders element indexWidth)

private abbrev succSchedules (element : SignalType) (indexWidth : Nat) :=
  (succDerivedRuleSchedules element indexWidth).schedules

private theorem succCoversChildren (element : SignalType) (indexWidth : Nat) :
    (succSchedules element indexWidth).CoversChildren :=
  (succDerivedRuleSchedules element indexWidth).coversChildren

private def valuesSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).inputs.Values
  | .value => inputs .values

private def indexSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (indexSplitter indexWidth).ports.inputs.Values
  | .value => inputs .index

private def indexLowerInputs (indexWidth : Nat)
    (split : (indexSplitter indexWidth).ports.outputs.Values) :
    (indexLowerCombiner indexWidth).ports.inputs.Values := fun lowerIndex =>
  split lowerIndex.castSucc

private def lowerInputs (element : SignalType) (indexWidth : Nat)
    (values : (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).outputs.Values)
    (lowerBits : (indexLowerCombiner indexWidth).ports.outputs.Values) :
    (ports element indexWidth).inputs.Values
  | .values => values .left
  | .index => lowerBits .value

private def upperInputs (element : SignalType) (indexWidth : Nat)
    (values : (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).outputs.Values)
    (lowerBits : (indexLowerCombiner indexWidth).ports.outputs.Values) :
    (ports element indexWidth).inputs.Values
  | .values => values .right
  | .index => lowerBits .value

private def muxInputs (element : SignalType) (indexWidth : Nat)
    (index : (indexSplitter indexWidth).ports.outputs.Values)
    (lower upper : (ports element indexWidth).outputs.Values) :
    (Mux.ports element).inputs.Values
  | .select => index (highIndex indexWidth)
  | .whenFalse => lower .result
  | .whenTrue => upper .result

private theorem succImplements (element : SignalType) (indexWidth : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody element indexWidth) (succChildContracts element indexWidth)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (succBody element indexWidth) layerChildren)
      (cycleContract element (indexWidth + 1)) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child,
      (succChildContracts element indexWidth child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (succChildContracts element indexWidth child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies childStates childStateSubsingleton
  have indexOutputs : (proposal.snd .indexSplit).outputs =
      (indexSplitter indexWidth).outputValues
        (indexSplitInputs element indexWidth inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (indexSplitter indexWidth) _ _ _).mp
      ((childMatches .indexSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (succBody element indexWidth)
        (fun child => (layerChildren child).moduleStructure)
        inputs proposal.snd .indexSplit = indexSplitInputs element indexWidth inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerOutputs : (proposal.snd .indexLower).outputs =
      (indexLowerCombiner indexWidth).outputValues
        (ProposedValues.childInputs (succBody element indexWidth)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.snd .indexLower) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (indexLowerCombiner indexWidth) _ _ _).mp
      ((childMatches .indexLower).1.1 Composition.SignalComponentRule.apply)

  have valuesEquation := (VectorSplit.outputRule_holds_iff element
    (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    _ SignalMap.emptyValues _).mp ((childMatches .valuesSplit).1.1 VectorSplit.Rule.apply)

  have lowerEquation := (outputRule_holds_iff element indexWidth
    _ SignalMap.emptyValues _).mp ((childMatches .lower).1.1 Rule.apply)

  have upperEquation := (outputRule_holds_iff element indexWidth
    _ SignalMap.emptyValues _).mp ((childMatches .upper).1.1 Rule.apply)

  have muxEquation := (Mux.selectRule_holds_iff element _ SignalMap.emptyValues _).mp
    ((childMatches .mux).1.1 Mux.Rule.select)

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change proposal.fst .result = _
    rw [show proposal.fst .result = (proposal.snd .mux).outputs .result by
      exact boundary .result]
    have valuesInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .valuesSplit =
          valuesSplitInputs element indexWidth inputs := by
      funext port; cases port; rfl
    have indexLowerInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .indexLower =
          indexLowerInputs indexWidth (proposal.snd .indexSplit).outputs := by
      funext lowerIndex; rfl
    have lowerInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .lower =
          lowerInputs element indexWidth (proposal.snd .valuesSplit).outputs
            (proposal.snd .indexLower).outputs := by
      funext port; cases port <;> rfl
    have upperInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .upper =
          upperInputs element indexWidth (proposal.snd .valuesSplit).outputs
            (proposal.snd .indexLower).outputs := by
      funext port; cases port <;> rfl
    have muxInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .mux =
          muxInputs element indexWidth (proposal.snd .indexSplit).outputs
            (proposal.snd .lower).outputs (proposal.snd .upper).outputs := by
      funext port; cases port <;> rfl
    rw [valuesInputsEquation] at valuesEquation
    rw [indexLowerInputsEquation] at lowerOutputs
    rw [lowerInputsEquation] at lowerEquation
    rw [upperInputsEquation] at upperEquation
    rw [muxInputsEquation] at muxEquation
    rw [muxEquation]
    have lowerValue : (proposal.snd .indexLower).outputs .value =
        fun lowerIndex => inputs .index lowerIndex.castSucc := by
      rw [congrFun lowerOutputs .value]
      funext lowerIndex
      change (proposal.snd .indexSplit).outputs lowerIndex.castSucc =
        inputs .index lowerIndex.castSucc
      rw [indexOutputs]
      rfl
    have highValue : (proposal.snd .indexSplit).outputs (highIndex indexWidth) =
        inputs .index (Fin.last indexWidth) := by
      rw [indexOutputs]
      rfl
    simp only [muxInputs]
    rw [lowerEquation, upperEquation]
    simp only [lowerInputs, upperInputs]
    rw [lowerValue, highValue]
    cases high : inputs .index (Fin.last indexWidth)
    · simp only [cond_false]
      rw [valuesEquation.1]
      simp [select, BitVector.toIndex,
        VectorSplit.leftPart, high]
      change inputs .values _ = inputs .values _
      apply congrArg (inputs .values)
      apply Fin.ext
      rfl
    · simp only [cond_true]
      rw [valuesEquation.2]
      simp [select, BitVector.toIndex,
        VectorSplit.rightPart, high, Fin.natAdd]
      change inputs .values _ = inputs .values _
      apply congrArg (inputs .values)
      apply Fin.ext
      rfl
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private noncomputable opaque succCertifiedLayer
    (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody element indexWidth)
      (succChildContracts element indexWidth) (cycleContract element (indexWidth + 1)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (succSchedules element indexWidth) (succCoversChildren element indexWidth)
    (fun _ _ _ => True) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (succImplements element indexWidth)

private noncomputable def succCertifiedChildren (element : SignalType)
    (indexWidth : Nat) (previous : Implementation element indexWidth) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody element indexWidth) (succChildContracts element indexWidth)
  | .valuesSplit =>
      (VectorSplit.certified element (BinaryToOneHot.size indexWidth)
        (BinaryToOneHot.size indexWidth)).certifiedStructure
  | .indexSplit => (indexSplitter indexWidth).certified.certifiedStructure
  | .indexLower => (indexLowerCombiner indexWidth).certified.certifiedStructure
  | .lower | .upper => previous.certified.certifiedStructure
  | .mux => (Mux.certified element).certifiedStructure

private noncomputable def succImplementation (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Implementation element (indexWidth + 1) :=
  ((succCertifiedLayer element indexWidth).certify
    (succCertifiedChildren element indexWidth previous)).transportStructure (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

noncomputable def implementation (element : SignalType) :
    (indexWidth : Nat) → Implementation element indexWidth
  | 0 => baseImplementation element
  | indexWidth + 1 =>
      succImplementation element indexWidth (implementation element indexWidth)

noncomputable def certification (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure element indexWidth)
      (cycleContract element indexWidth) := implementation element indexWidth

noncomputable def certified (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports element indexWidth) :=
  (certification element indexWidth).bundle

end Silean.Modules.CombMuxTree

namespace Silean.Modules.CombMuxTree.Naming

open Silean Silean.Naming

def portsWithNaming (element : SignalType) (indexWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Modules.CombMuxTree.ports element indexWidth) where
  inputs := ⟨fun | .values => "values" | .index => "index"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .values => .vector elementNaming
    | .index => .vector .bit
  outputTypes := fun | .result => elementNaming

def ports (element : SignalType) (indexWidth : Nat) :
    ModulePortsNaming (Modules.CombMuxTree.ports element indexWidth) :=
  portsWithNaming element indexWidth (.positional element)

def namingWith (element : SignalType) : (indexWidth : Nat) →
    SignalTypeNaming element →
      ModuleNaming (Modules.CombMuxTree.moduleStructure element indexWidth)
  | 0, elementNaming => by
      rw [Modules.CombMuxTree.moduleStructure.eq_def]
      exact .composite
        ⟨"comb_mux_tree", "base", [.shape element]⟩
        (portsWithNaming element 0 elementNaming)
        (fun | Modules.CombMuxTree.BaseInstance.split => "split_value")
        (fun
          | Modules.CombMuxTree.BaseInstance.split =>
              Silean.Naming.SignalAdapter.splitterWithNaming
                (Composition.SignalSplitter.vector 1 element)
                (SignalTypeNaming.vector elementNaming))
  | indexWidth + 1, elementNaming => by
      rw [Modules.CombMuxTree.moduleStructure.eq_def]
      exact .composite
        ⟨"comb_mux_tree", "recursive", [.shape element, .natural (indexWidth + 1)]⟩
        (portsWithNaming element (indexWidth + 1) elementNaming)
        (fun
          | .valuesSplit => "split_values"
          | .indexSplit => "split_index"
          | .indexLower => "combine_index_lower"
          | .lower => "select_lower"
          | .upper => "select_upper"
          | .mux => "mux")
        (fun
          | .valuesSplit => VectorSplit.Naming.namingWith element
              (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
              elementNaming
          | .indexSplit => Silean.Naming.SignalAdapter.splitter
              (Modules.CombMuxTree.indexSplitter indexWidth)
          | .indexLower => Silean.Naming.SignalAdapter.combiner
              (Modules.CombMuxTree.indexLowerCombiner indexWidth)
          | .lower | .upper => namingWith element indexWidth elementNaming
          | .mux => Mux.Naming.namingWith element elementNaming)

def naming (element : SignalType) (indexWidth : Nat) :
    ModuleNaming (Modules.CombMuxTree.moduleStructure element indexWidth) :=
  namingWith element indexWidth (.positional element)

def namedModule (element : SignalType) (indexWidth : Nat) : NamedModule where
  ports := Modules.CombMuxTree.ports element indexWidth
  moduleStructure := Modules.CombMuxTree.moduleStructure element indexWidth
  naming := naming element indexWidth

end Silean.Modules.CombMuxTree.Naming
