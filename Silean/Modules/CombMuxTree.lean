import Silean.CertifiedSchedule
import Silean.Modules.BinaryToOneHot
import Silean.Modules.Mux
import Silean.Modules.VectorSplit
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.CombMuxTree

open Silean

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
    CycleOutputRule (ports element indexWidth) emptySignalMap
      { inputTypes := .cons (.vector (BinaryToOneHot.size indexWidth) element)
          (.cons (.vector indexWidth .bit) .nil)
        outputTypes := .cons element .nil } where
  readsInputs := ((inputMap element indexWidth).select .index).prepend .values
  writesOutputs := (outputMap element).select .result
  target | (values, (index, ())), _ => (select indexWidth values index, ())

@[reducible] def cycleContract (element : SignalType) (indexWidth : Nat) :
    ModuleCycleContract (ports element indexWidth) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule element indexWidth⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element indexWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element indexWidth).outputs.Values) :
    (outputRule element indexWidth).Holds inputs state outputs ↔
      outputs .result = select indexWidth (inputs .values) (inputs .index) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
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

/-! Width zero has one value and no selector bits. -/

private def baseSplitter (element : SignalType) : SignalSplitter := .vector 1 element

private inductive BaseInstance | split
deriving Enumeration

@[reducible] private def baseInstances (element : SignalType) : Instances :=
  EnumeratedMap.of BaseInstance fun | .split => (baseSplitter element).ports

@[reducible] private def baseContext (element : SignalType) : EndpointContext where
  ports := ports element 0
  instances := baseInstances element

private def baseWiring (element : SignalType) :
    Wiring (baseContext element).ports (baseContext element).instances where
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

private def indexSplitter (indexWidth : Nat) : SignalSplitter :=
  .vector (indexWidth + 1) .bit
private def indexLowerCombiner (indexWidth : Nat) : SignalCombiner :=
  .vector indexWidth .bit
private def highIndex (indexWidth : Nat) : (indexSplitter indexWidth).ports.outputs.Label :=
  Fin.last indexWidth

inductive SuccInstance
  | valuesSplit
  | indexSplit
  | indexLower
  | lower
  | upper
  | mux
deriving Enumeration

@[reducible] def succInstances (element : SignalType) (indexWidth : Nat) : Instances :=
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
  instances := succInstances element indexWidth

def succWiring (element : SignalType) (indexWidth : Nat) :
    Wiring (succContext element indexWidth).ports
      (succContext element indexWidth).instances where
  moduleOutput | .result => (succContext element indexWidth).instanceOutput .mux .result
  instanceInput
    | .valuesSplit, .value =>
        (succContext element indexWidth).moduleInput .values
    | .indexSplit, .value =>
        (succContext element indexWidth).moduleInput .index
    | .indexLower, lowerIndex =>
        (succContext element indexWidth).instanceOutput .indexSplit lowerIndex.castSucc
    | .lower, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .left
    | .lower, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
    | .upper, .values =>
        (succContext element indexWidth).instanceOutput .valuesSplit .right
    | .upper, .index =>
        (succContext element indexWidth).instanceOutput .indexLower .value
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
  ModuleCycleCertification (moduleStructure element indexWidth)
    (cycleContract element indexWidth)

private def Implementation.certified
    (implementation : Implementation element indexWidth) :
    ModuleCycleCertified (ports element indexWidth) := implementation.bundle

@[reducible] private def baseChildren (element : SignalType) :
    Certified.Children (baseBody element)
  | .split => (baseSplitter element).certified

private abbrev baseOccurrence (element : SignalType) :
    Certified.RuleOccurrence (baseChildren element) :=
  ⟨.split, SignalComponentRule.apply⟩

private def baseOutputSchedule (element : SignalType) :
    Certified.OutputSchedule (baseBody element) (baseChildren element)
      (cycleContract element 0) .apply :=
  .call (baseOccurrence element)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, baseBody, baseWiring,
        baseContext, EndpointContext.moduleInput])
    (by simp)
    (.done (by
      intro output _
      cases output
      exact ⟨SignalComponentRule.apply, by simp, by
        change (⟨0, by omega⟩ : Fin 1) ∈
          (baseOccurrence element).writes
        change (⟨0, by omega⟩ : Fin 1) ∈
          (baseSplitter element).ports.outputs.allSelection.labels
        rw [SignalMap.allSelection_labels]
        exact ListIndex.get_eq
          ((baseSplitter element).ports.outputs.labels.locate ⟨0, by omega⟩) ▸
            List.get_mem _ _⟩))

private def baseStateSchedule (element : SignalType) :
    Certified.StateSchedule (baseBody element) (baseChildren element) :=
  .done (by
    intro child input member
    cases child
    change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
    exact nomatch member)

private def baseSchedules (element : SignalType) :
    Certified.RuleSchedules (baseBody element) (baseChildren element)
      (cycleContract element 0) where
  output | .apply => baseOutputSchedule element
  state := baseStateSchedule element

private theorem baseCoversChildren (element : SignalType) :
    (baseSchedules element).CoversChildren := by
  intro child rule
  cases child
  change SignalComponentRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs (baseSchedules element) .apply
  change baseOccurrence element ∈ (baseOutputSchedule element).finalAvailability
  simp [baseOutputSchedule, Certified.Schedule.finalAvailability]

private def baseSplitInputs (element : SignalType)
    (inputs : (ports element 0).inputs.Values) :
    (baseSplitter element).ports.inputs.Values
  | .value => inputs .values

private theorem baseHasStructuralResult (element : SignalType)
    (inputs : (ports element 0).inputs.Values)
    (state : (baseModuleStructure element).State) :
    ∃ proposal, (baseModuleStructure element).IsSolution inputs state proposal := by
  rcases (baseChildren element .split).hasStructuralResult
      (baseSplitInputs element inputs) (state .split) with ⟨split, splitSatisfies⟩
  let children : (child : BaseInstance) →
      ProposedValues (Certified.childStructure (baseChildren element) child)
    | .split => split
  let outputs : (ports element 0).outputs.Values := fun
    | .result => split.outputs ⟨0, by omega⟩
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child
    change (baseChildren element .split).moduleStructure.IsSolution
      (ProposedValues.childInputs (baseBody element) _ inputs children .split)
      (state .split) split
    rw [show ProposedValues.childInputs (baseBody element) _ inputs children .split =
        baseSplitInputs element inputs by funext port; cases port; rfl]
    exact splitSatisfies

private theorem baseImplements (element : SignalType) :
    Implements (baseModuleStructure element) (cycleContract element 0)
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have splitOutputs : (children .split).outputs =
      (baseSplitter element).outputValues (baseSplitInputs element inputs) :=
    childSatisfies .split
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

private def baseImplementation (element : SignalType) : Implementation element 0 where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := baseHasStructuralResult element
  structuralResultUnique := (baseSchedules element).hasAtMostOneSolution
    (baseCoversChildren element)
  implements := baseImplements element

@[reducible] private noncomputable def succChildren (element : SignalType)
    (indexWidth : Nat) (previous : Implementation element indexWidth) :
    Certified.Children (succBody element indexWidth)
  | .valuesSplit => VectorSplit.certified element
      (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
  | .indexSplit => (indexSplitter indexWidth).certified
  | .indexLower => (indexLowerCombiner indexWidth).certified
  | .lower | .upper => previous.certified
  | .mux => Mux.certified element

private abbrev valuesSplitOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.valuesSplit, VectorSplit.Rule.apply⟩
private abbrev indexSplitOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.indexSplit, SignalComponentRule.apply⟩
private abbrev indexLowerOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.indexLower, SignalComponentRule.apply⟩
private abbrev lowerOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.lower, Rule.apply⟩
private abbrev upperOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.upper, Rule.apply⟩
private abbrev muxOccurrence (element) (indexWidth)
    (previous : Implementation element indexWidth) :
    Certified.RuleOccurrence (succChildren element indexWidth previous) :=
  ⟨.mux, Mux.Rule.select⟩

private theorem indexSplitWrites (element) (indexWidth)
    (previous : Implementation element indexWidth)
    (index : Fin (indexWidth + 1)) :
    index ∈ (indexSplitOccurrence element indexWidth previous).writes := by
  change index ∈ (indexSplitter indexWidth).ports.outputs.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq
    ((indexSplitter indexWidth).ports.outputs.labels.locate index) ▸
      List.get_mem _ _

private def succOutputSchedule (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Certified.OutputSchedule (succBody element indexWidth)
      (succChildren element indexWidth previous)
      (cycleContract element (indexWidth + 1)) .apply :=
  .call (valuesSplitOccurrence element indexWidth previous)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, succBody, succWiring,
        succContext, EndpointContext.moduleInput])
    (by simp)
  (.call (indexSplitOccurrence element indexWidth previous)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalSelection.prepend, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, succBody, succWiring,
        succContext, EndpointContext.moduleInput])
    (by simp)
  (.call (indexLowerOccurrence element indexWidth previous)
    (by intro lowerIndex _; exact ⟨SignalComponentRule.apply, by simp,
      indexSplitWrites element indexWidth previous lowerIndex.castSucc⟩)
    (by simp)
  (.call (lowerOccurrence element indexWidth previous)
    (by intro input _; cases input with
      | values => exact ⟨VectorSplit.Rule.apply, by simp,
          by change VectorSplit.Output.left ∈ [.left, .right]; simp⟩
      | index => exact ⟨SignalComponentRule.apply, by simp,
          by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩)
    (by simp)
  (.call (upperOccurrence element indexWidth previous)
    (by intro input _; cases input with
      | values => exact ⟨VectorSplit.Rule.apply, by simp,
          by change VectorSplit.Output.right ∈ [.left, .right]; simp⟩
      | index => exact ⟨SignalComponentRule.apply, by simp,
          by change AggregatePort.value ∈ [AggregatePort.value]; simp⟩)
    (by simp)
  (.call (muxOccurrence element indexWidth previous)
    (by intro input _; cases input with
      | select => exact ⟨SignalComponentRule.apply, by simp,
          indexSplitWrites element indexWidth previous (highIndex indexWidth)⟩
      | whenFalse => exact ⟨Rule.apply, by simp,
          by change Output.result ∈ [Output.result]; simp⟩
      | whenTrue => exact ⟨Rule.apply, by simp,
          by change Output.result ∈ [Output.result]; simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output
    exact ⟨Mux.Rule.select, by simp,
      by change Mux.Output.result ∈ [Mux.Output.result]; simp⟩)))))))

private def succStateSchedule (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Certified.StateSchedule (succBody element indexWidth)
      (succChildren element indexWidth previous) :=
  .done (by
    intro child input member
    cases child with
    | valuesSplit =>
        change input ∈ (VectorSplit.cycleContract _ _ _).stateRule.readsInputs.labels at member
        exact nomatch member
    | indexSplit | indexLower =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | lower | upper =>
        change input ∈ (cycleContract element indexWidth).stateRule.readsInputs.labels at member
        exact nomatch member
    | mux =>
        change input ∈ (Mux.cycleContract element).stateRule.readsInputs.labels at member
        exact nomatch member)

private def succSchedules (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Certified.RuleSchedules (succBody element indexWidth)
      (succChildren element indexWidth previous)
      (cycleContract element (indexWidth + 1)) where
  output | .apply => succOutputSchedule element indexWidth previous
  state := succStateSchedule element indexWidth previous

private theorem succCoversChildren (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    (succSchedules element indexWidth previous).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (succSchedules element indexWidth previous) .apply
  cases child with
  | valuesSplit =>
      change VectorSplit.Rule at rule; cases rule
      change valuesSplitOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | indexSplit =>
      change SignalComponentRule at rule; cases rule
      change indexSplitOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | indexLower =>
      change SignalComponentRule at rule; cases rule
      change indexLowerOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | lower =>
      change Rule at rule; cases rule
      change lowerOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | upper =>
      change Rule at rule; cases rule
      change upperOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | mux =>
      change Mux.Rule at rule; cases rule
      change muxOccurrence element indexWidth previous ∈
        (succOutputSchedule element indexWidth previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]

private def valuesSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).inputs.Values
  | .value => inputs .values

private def indexSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (indexSplitter indexWidth).ports.inputs.Values
  | .value => inputs .index

private noncomputable def indexLowerInputs (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth)
    (split : ProposedValues
      (succChildren element indexWidth previous .indexSplit).moduleStructure) :
    (indexLowerCombiner indexWidth).ports.inputs.Values := fun lowerIndex =>
  split.outputs lowerIndex.castSucc

private noncomputable def lowerInputs (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth)
    (values : ProposedValues
      (succChildren element indexWidth previous .valuesSplit).moduleStructure)
    (lowerBits : ProposedValues
      (succChildren element indexWidth previous .indexLower).moduleStructure) :
    (ports element indexWidth).inputs.Values
  | .values => values.outputs .left
  | .index => lowerBits.outputs .value

private noncomputable def upperInputs (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth)
    (values : ProposedValues
      (succChildren element indexWidth previous .valuesSplit).moduleStructure)
    (lowerBits : ProposedValues
      (succChildren element indexWidth previous .indexLower).moduleStructure) :
    (ports element indexWidth).inputs.Values
  | .values => values.outputs .right
  | .index => lowerBits.outputs .value

private noncomputable def muxInputs (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth)
    (index : ProposedValues
      (succChildren element indexWidth previous .indexSplit).moduleStructure)
    (lower : ProposedValues
      (succChildren element indexWidth previous .lower).moduleStructure)
    (upper : ProposedValues
      (succChildren element indexWidth previous .upper).moduleStructure) :
    (Mux.ports element).inputs.Values
  | .select => index.outputs (highIndex indexWidth)
  | .whenFalse => lower.outputs .result
  | .whenTrue => upper.outputs .result

private theorem succHasStructuralResult (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth)
    (inputs : (ports element (indexWidth + 1)).inputs.Values)
    (state : (Certified.moduleStructure (succBody element indexWidth)
      (succChildren element indexWidth previous)).State) :
    ∃ proposal, (Certified.moduleStructure (succBody element indexWidth)
      (succChildren element indexWidth previous)).IsSolution inputs state proposal := by
  rcases (succChildren element indexWidth previous .valuesSplit).hasStructuralResult
      (valuesSplitInputs element indexWidth inputs) (state .valuesSplit) with
    ⟨values, valuesSatisfy⟩
  rcases (succChildren element indexWidth previous .indexSplit).hasStructuralResult
      (indexSplitInputs element indexWidth inputs) (state .indexSplit) with
    ⟨index, indexSatisfies⟩
  rcases (succChildren element indexWidth previous .indexLower).hasStructuralResult
      (indexLowerInputs element indexWidth previous index) (state .indexLower) with
    ⟨lowerBits, indexLowerSatisfies⟩
  rcases (succChildren element indexWidth previous .lower).hasStructuralResult
      (lowerInputs element indexWidth previous values lowerBits) (state .lower) with
    ⟨lower, lowerSatisfies⟩
  rcases (succChildren element indexWidth previous .upper).hasStructuralResult
      (upperInputs element indexWidth previous values lowerBits) (state .upper) with
    ⟨upper, upperSatisfies⟩
  rcases (succChildren element indexWidth previous .mux).hasStructuralResult
      (muxInputs element indexWidth previous index lower upper) (state .mux) with
    ⟨mux, muxSatisfies⟩
  let proposals : (child : SuccInstance) →
      ProposedValues (Certified.childStructure
        (succChildren element indexWidth previous) child)
    | .valuesSplit => values
    | .indexSplit => index
    | .indexLower => lowerBits
    | .lower => lower
    | .upper => upper
    | .mux => mux
  let outputs : (ports element (indexWidth + 1)).outputs.Values := fun
    | .result => mux.outputs .result
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child <;>
      change (succChildren element indexWidth previous _).moduleStructure.IsSolution
        (ProposedValues.childInputs (succBody element indexWidth) _ inputs proposals _)
        (state _) _
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .valuesSplit = valuesSplitInputs element indexWidth inputs by
        funext port; cases port; rfl]
      exact valuesSatisfy
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .indexSplit = indexSplitInputs element indexWidth inputs by
        funext port; cases port; rfl]
      exact indexSatisfies
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .indexLower =
            indexLowerInputs element indexWidth previous index by
        funext lowerIndex; rfl]
      exact indexLowerSatisfies
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .lower = lowerInputs element indexWidth previous values lowerBits by
        funext port; cases port <;> rfl]
      exact lowerSatisfies
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .upper = upperInputs element indexWidth previous values lowerBits by
        funext port; cases port <;> rfl]
      exact upperSatisfies
    · rw [show ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposals .mux = muxInputs element indexWidth previous index lower upper by
        funext port; cases port <;> rfl]
      exact muxSatisfies

private theorem succImplements (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Implements (Certified.moduleStructure (succBody element indexWidth)
      (succChildren element indexWidth previous))
      (cycleContract element (indexWidth + 1)) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childSatisfies := satisfies.2
  have indexOutputs : (proposal.snd .indexSplit).outputs =
      (indexSplitter indexWidth).outputValues
        (indexSplitInputs element indexWidth inputs) := childSatisfies .indexSplit
  have lowerOutputs : (proposal.snd .indexLower).outputs =
      (indexLowerCombiner indexWidth).outputValues
        (ProposedValues.childInputs (succBody element indexWidth) _
          inputs proposal.snd .indexLower) := childSatisfies .indexLower

  rcases (succChildren element indexWidth previous .valuesSplit).hasCorrespondingState
      (structuralState .valuesSplit) with ⟨valuesState, valuesCorresponds⟩
  rcases Certified.childImplements (succChildren element indexWidth previous) inputs
      structuralState proposal satisfies .valuesSplit valuesState valuesCorresponds with
    ⟨_, valuesEvaluate, _⟩
  have valuesEquation := (VectorSplit.outputRule_holds_iff element
    (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    _ valuesState _).mp (valuesEvaluate.1 VectorSplit.Rule.apply)

  rcases (succChildren element indexWidth previous .lower).hasCorrespondingState
      (structuralState .lower) with ⟨lowerState, lowerCorresponds⟩
  rcases Certified.childImplements (succChildren element indexWidth previous) inputs
      structuralState proposal satisfies .lower lowerState lowerCorresponds with
    ⟨_, lowerEvaluate, _⟩
  have lowerEquation := (outputRule_holds_iff element indexWidth
    _ lowerState _).mp (lowerEvaluate.1 Rule.apply)

  rcases (succChildren element indexWidth previous .upper).hasCorrespondingState
      (structuralState .upper) with ⟨upperState, upperCorresponds⟩
  rcases Certified.childImplements (succChildren element indexWidth previous) inputs
      structuralState proposal satisfies .upper upperState upperCorresponds with
    ⟨_, upperEvaluate, _⟩
  have upperEquation := (outputRule_holds_iff element indexWidth
    _ upperState _).mp (upperEvaluate.1 Rule.apply)

  rcases (succChildren element indexWidth previous .mux).hasCorrespondingState
      (structuralState .mux) with ⟨muxState, muxCorresponds⟩
  rcases Certified.childImplements (succChildren element indexWidth previous) inputs
      structuralState proposal satisfies .mux muxState muxCorresponds with
    ⟨_, muxEvaluate, _⟩
  have muxEquation := (Mux.selectRule_holds_iff element _ muxState _).mp
    (muxEvaluate.1 Mux.Rule.select)

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
          indexLowerInputs element indexWidth previous (proposal.snd .indexSplit) := by
      funext lowerIndex; rfl
    have lowerInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .lower =
          lowerInputs element indexWidth previous (proposal.snd .valuesSplit)
            (proposal.snd .indexLower) := by
      funext port; cases port <;> rfl
    have upperInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .upper =
          upperInputs element indexWidth previous (proposal.snd .valuesSplit)
            (proposal.snd .indexLower) := by
      funext port; cases port <;> rfl
    have muxInputsEquation : ProposedValues.childInputs
        (succBody element indexWidth) _ inputs proposal.snd .mux =
          muxInputs element indexWidth previous (proposal.snd .indexSplit)
            (proposal.snd .lower) (proposal.snd .upper) := by
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

private theorem succModuleStructure_eq (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    moduleStructure element (indexWidth + 1) =
      Certified.moduleStructure (succBody element indexWidth)
        (succChildren element indexWidth previous) := by
  change ModuleStructure.composite (succBody element indexWidth) (fun
    | .valuesSplit => VectorSplit.moduleStructure element
        (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    | .indexSplit => (indexSplitter indexWidth).certified.moduleStructure
    | .indexLower => (indexLowerCombiner indexWidth).certified.moduleStructure
    | .lower | .upper => moduleStructure element indexWidth
    | .mux => Mux.moduleStructure element) = _
  unfold Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

private def succImplementation (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Implementation element (indexWidth + 1) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := by
    rw [succModuleStructure_eq element indexWidth previous]
    exact succHasStructuralResult element indexWidth previous
  structuralResultUnique := by
    rw [succModuleStructure_eq element indexWidth previous]
    exact (succSchedules element indexWidth previous).hasAtMostOneSolution
      (succCoversChildren element indexWidth previous)
  implements := by
    rw [succModuleStructure_eq element indexWidth previous]
    exact succImplements element indexWidth previous

noncomputable def implementation (element : SignalType) :
    (indexWidth : Nat) → Implementation element indexWidth
  | 0 => baseImplementation element
  | indexWidth + 1 =>
      succImplementation element indexWidth (implementation element indexWidth)

noncomputable def certification (element : SignalType) (indexWidth : Nat) :
    ModuleCycleCertification (moduleStructure element indexWidth)
      (cycleContract element indexWidth) := implementation element indexWidth

noncomputable def certified (element : SignalType) (indexWidth : Nat) :
    ModuleCycleCertified (ports element indexWidth) :=
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
                (SignalSplitter.vector 1 element)
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
