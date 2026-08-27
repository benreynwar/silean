import Silean2.CertifiedSchedule
import Silean2.Foundation.BitVector
import Silean2.Modules.Constant
import Silean2.Modules.Mask
import Silean2.Modules.VectorConcat
import Silean2.Naming.PrimitiveNaming
import Silean2.Naming.SignalAdapterNaming
import Silean2.Primitives.Not

namespace Silean2.Modules.BinaryToOneHot

open Silean2

inductive Input | value
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun | .value => .vector width .bit

abbrev size := BitVector.cardinality

@[simp] theorem size_eq_pow (width : Nat) : size width = 2 ^ width :=
  BitVector.cardinality_eq_pow width

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .result => .vector (size width) .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

/-! Bit index `i` has weight `2 ^ i`. The definition is deliberately
contract-level Lean code; it does not mention the structural hierarchy. -/
def decode : (width : Nat) → (Fin width → Bool) → Fin (size width) → Bool
  | 0, _ => fun _ => true
  | width + 1, bits => fun index =>
      Fin.addCases
        (fun lower => !bits (Fin.last width) &&
          decode width (fun i => bits i.castSucc) lower)
        (fun upper => bits (Fin.last width) &&
          decode width (fun i => bits i.castSucc) upper)
        index

private theorem castAdd_injective {n : Nat} (left right : Fin n) :
    Fin.castAdd n left = Fin.castAdd n right ↔ left = right := by
  constructor
  · intro equal; apply Fin.ext
    simpa [Fin.castAdd] using congrArg Fin.val equal
  · intro equal; cases equal; rfl

private theorem natAdd_injective {n : Nat} (left right : Fin n) :
    Fin.natAdd n left = Fin.natAdd n right ↔ left = right := by
  constructor
  · intro equal; apply Fin.ext
    simpa [Fin.natAdd] using congrArg Fin.val equal
  · intro equal; cases equal; rfl

private theorem castAdd_ne_natAdd {n : Nat} (left right : Fin n) :
    Fin.castAdd n left ≠ Fin.natAdd n right := by
  intro equal
  have values := congrArg Fin.val equal
  have bound := left.isLt
  simp [Fin.castAdd, Fin.natAdd] at values
  omega

private theorem addNat_eq_natAdd {n : Nat} (index : Fin n) :
    index.addNat n = Fin.natAdd n index := by
  apply Fin.ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

private theorem castAdd_ne_addNat {n : Nat} (left right : Fin n) :
    Fin.castAdd n left ≠ right.addNat n := by
  rw [addNat_eq_natAdd]
  exact castAdd_ne_natAdd left right

private theorem addNat_ne_castAdd {n : Nat} (left right : Fin n) :
    left.addNat n ≠ Fin.castAdd n right :=
  Ne.symm (castAdd_ne_addNat right left)

private theorem addNat_injective {n : Nat} (left right : Fin n) :
    left.addNat n = right.addNat n ↔ left = right := by
  rw [addNat_eq_natAdd, addNat_eq_natAdd]
  exact natAdd_injective left right

private theorem addCases_addNat {n : Nat} (left right : Fin n → α)
    (index : Fin n) :
    Fin.addCases left right (index.addNat n) = right index := by
  rw [addNat_eq_natAdd]
  exact Fin.addCases_right index

theorem decode_eq_true_iff : ∀ (width : Nat) (bits : Fin width → Bool)
    (index : Fin (size width)),
    decode width bits index = true ↔ index = BitVector.toIndex width bits
  | 0, _, index => by
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  | width + 1, bits, index => by
      refine Fin.addCases ?_ ?_ index
      · intro lower
        cases high : bits (Fin.last width) <;>
          simp [decode, BitVector.toIndex, high, decode_eq_true_iff,
            castAdd_injective, castAdd_ne_addNat]
      · intro upper
        cases high : bits (Fin.last width)
        · simp [decode, BitVector.toIndex, high, addCases_addNat,
            addNat_ne_castAdd]
        · simp [decode, BitVector.toIndex, high, decode_eq_true_iff,
            addCases_addNat, addNat_injective]

def oneHot (width : Nat) (bits : Fin width → Bool) : Fin (size width) → Bool :=
  fun index => decide (index.val = BitVector.toNat width bits)

theorem oneHot_eq_decode (width : Nat) (bits : Fin width → Bool) :
    oneHot width bits = decode width bits := by
  funext index
  apply Bool.eq_iff_iff.mpr
  rw [decode_eq_true_iff]
  simp only [oneHot, decide_eq_true_iff]
  constructor
  · intro equal
    apply Fin.ext
    simpa [BitVector.toIndex_val] using equal
  · intro equal
    simpa [BitVector.toIndex_val] using congrArg Fin.val equal

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    CycleOutputRule (ports width) emptySignalMap
      { inputTypes := .cons (.vector width .bit) .nil
        outputTypes := .cons (.vector (size width) .bit) .nil } where
  readsInputs := (inputMap width).select .value
  writesOutputs := (outputMap width).select .result
  target | (value, ()), _ => (oneHot width value, ())

@[reducible] def cycleContract (width : Nat) : ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule width⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = oneHot width (inputs .value) := by
  simp [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

theorem result_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs)
    (index : Fin (size width)) :
    outputs .result index = oneHot width (inputs .value) index := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]

theorem result_eq_true_iff_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs)
    (index : Fin (size width)) :
    outputs .result index = true ↔
      index.val = BitVector.toNat width (inputs .value) := by
  rw [result_of_holds width inputs state outputs holds index]
  exact decide_eq_true_iff

/-! Width zero is the one-element constant vector `[true]`. A successor width
splits off the highest-index bit, rebuilds the lower-bit vector, recursively
decodes it, masks two copies with the high bit and its inverse, then joins
the halves. -/

private def baseValue : (SignalType.vector 1 .bit).Denote := fun _ => true

private inductive BaseInstance | constant
deriving Enumeration

@[reducible] private def baseInstances : Instances :=
  EnumeratedMap.of BaseInstance fun
    | .constant => Modules.Constant.ports (.vector 1 .bit)

@[reducible] private def baseContext : EndpointContext where
  ports := ports 0
  instances := baseInstances

private def baseWiring : Wiring baseContext.ports baseContext.instances where
  moduleOutput | .result => baseContext.instanceOutput .constant .output
  instanceInput | .constant, impossible => nomatch impossible

@[reducible] private def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

private def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .constant => Modules.Constant.moduleStructure (.vector 1 .bit) baseValue

private def splitter (width : Nat) : SignalSplitter := .vector (width + 1) .bit
private def lowerCombiner (width : Nat) : SignalCombiner := .vector width .bit
private def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

inductive SuccInstance
  | split
  | lowerBits
  | decode
  | invert
  | lowerMask
  | upperMask
  | concat
deriving Enumeration

@[reducible] def succInstances (width : Nat) : Instances :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .decode => ports width
    | .invert => Primitives.not.ports
    | .lowerMask | .upperMask => Modules.Mask.ports (.vector (size width) .bit)
    | .concat => Modules.VectorConcat.ports .bit (size width) (size width)

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instances := succInstances width

def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instances where
  moduleOutput
    | .result => (succContext width).instanceOutput .concat .result
  instanceInput
    | .split, .value => (succContext width).moduleInput .value
    | .lowerBits, index =>
        (succContext width).instanceOutput .split index.castSucc
    | .decode, .value =>
        (succContext width).instanceOutput .lowerBits .value
    | .invert, .input =>
        (succContext width).instanceOutput .split (highIndex width)
    | .lowerMask, .value =>
        (succContext width).instanceOutput .decode .result
    | .lowerMask, .mask =>
        (succContext width).instanceOutput .invert .output
    | .upperMask, .value =>
        (succContext width).instanceOutput .decode .result
    | .upperMask, .mask =>
        (succContext width).instanceOutput .split (highIndex width)
    | .concat, .left =>
        (succContext width).instanceOutput .lowerMask .result
    | .concat, .right =>
        (succContext width).instanceOutput .upperMask .result

@[reducible] def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .split => (splitter width).certified.moduleStructure
      | .lowerBits => (lowerCombiner width).certified.moduleStructure
      | .decode => moduleStructure width
      | .invert => Primitives.notCertified.moduleStructure
      | .lowerMask | .upperMask =>
          Modules.Mask.moduleStructure (.vector (size width) .bit)
      | .concat => Modules.VectorConcat.moduleStructure .bit (size width) (size width)

private abbrev Implementation (width : Nat) :=
  ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private noncomputable def baseChildren : Certified.Children baseBody
  | .constant => Modules.Constant.certified (.vector 1 .bit) baseValue

private abbrev baseOccurrence : Certified.RuleOccurrence baseChildren :=
  ⟨.constant, Primitives.ConstantRule.apply⟩

private def baseOutputSchedule : Certified.OutputSchedule baseBody baseChildren
    (cycleContract 0) .apply :=
  .call baseOccurrence
    (by intro input member; exact nomatch input)
    (by simp)
    (.done (by
      intro output _
      cases output
      exact ⟨Primitives.ConstantRule.apply, by simp,
        by change Primitives.SingleOutput.output ∈ [.output]; simp⟩))

private def baseStateSchedule : Certified.StateSchedule baseBody baseChildren :=
  .done (by
    intro child input member
    cases child
    change input ∈ (CycleStateRule.empty
      (Modules.Constant.ports (.vector 1 .bit))).readsInputs.labels at member
    exact nomatch member)

private def baseSchedules : Certified.RuleSchedules baseBody baseChildren
    (cycleContract 0) where
  output | .apply => baseOutputSchedule
  state := baseStateSchedule

private theorem baseCoversChildren : baseSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.ConstantRule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs baseSchedules .apply
  change baseOccurrence ∈ baseOutputSchedule.finalAvailability
  simp [baseOutputSchedule, Certified.Schedule.finalAvailability]

private def baseChildInputs :
    (Modules.Constant.ports (.vector 1 .bit)).inputs.Values :=
  fun impossible => nomatch impossible

private theorem baseHasStructuralResult (inputs : (ports 0).inputs.Values)
    (state : baseModuleStructure.State) :
    ∃ proposal, baseModuleStructure.IsSolution inputs state proposal := by
  rcases (baseChildren .constant).hasStructuralResult baseChildInputs
      (state .constant) with ⟨constant, constantSatisfies⟩
  let children : (child : BaseInstance) →
      ProposedValues (Certified.childStructure baseChildren child)
    | .constant => constant
  let outputs : (ports 0).outputs.Values := fun
    | .result => constant.outputs .output
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child
    change (baseChildren .constant).moduleStructure.IsSolution
      (ProposedValues.childInputs baseBody _ inputs children .constant)
      (state .constant) constant
    rw [show ProposedValues.childInputs baseBody _ inputs children .constant =
        baseChildInputs by funext impossible; exact nomatch impossible]
    exact constantSatisfies

private theorem baseImplements : Implements baseModuleStructure
    (cycleContract 0) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  rcases (baseChildren .constant).hasCorrespondingState
      (structuralState .constant) with ⟨childState, childCorresponds⟩
  have childImplements := Certified.childImplements baseChildren inputs
    structuralState proposal satisfies .constant childState childCorresponds
  rcases childImplements with ⟨_, childEvaluates, _⟩
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext index
    change proposal.fst .result index = _
    have boundaryResult := boundary .result
    rw [congrFun boundaryResult index]
    have constantRule := (Modules.Constant.outputRule_holds_iff
      (.vector 1 .bit) baseValue _ childState _).mp
      (childEvaluates.1 Primitives.ConstantRule.apply)
    change (proposal.snd .constant).outputs .output index = _
    exact (congrFun constantRule index).trans (by
      simp [baseValue, oneHot, BitVector.toNat])
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private def baseImplementation : Implementation 0 where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := baseHasStructuralResult
  structuralResultUnique := baseSchedules.hasAtMostOneSolution baseCoversChildren
  implements := baseImplements

@[reducible] private noncomputable def succChildren (width : Nat)
    (previous : Implementation width) : Certified.Children (succBody width)
  | .split => (splitter width).certified
  | .lowerBits => (lowerCombiner width).certified
  | .decode => previous.certified
  | .invert => Primitives.notCertified
  | .lowerMask | .upperMask => Modules.Mask.certified (.vector (size width) .bit)
  | .concat => Modules.VectorConcat.certified .bit (size width) (size width)

private abbrev splitOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.split, SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.lowerBits, SignalComponentRule.apply⟩
private abbrev decodeOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.decode, Rule.apply⟩
private abbrev invertOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.invert, Primitives.NotRule.apply⟩
private abbrev lowerOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.lowerMask, Modules.Mask.Rule.apply⟩
private abbrev upperOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.upperMask, Modules.Mask.Rule.apply⟩
private abbrev concatOccurrence (width) (previous : Implementation width) :
    Certified.RuleOccurrence (succChildren width previous) :=
  ⟨.concat, Modules.VectorConcat.Rule.apply⟩

private def succOutputSchedule (width : Nat) (previous : Implementation width) :
    Certified.OutputSchedule (succBody width) (succChildren width previous)
      (cycleContract (width + 1)) .apply :=
  .call (splitOccurrence width previous)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalMap.select,
        SignalSelection.labels, Certified.sourceAvailable, succBody,
        succWiring, succContext, EndpointContext.moduleInput])
    (by simp)
  (.call (lowerBitsOccurrence width previous)
    (by
      intro index _
      exact ⟨SignalComponentRule.apply, by simp, by
        change index.castSucc ∈ (splitOccurrence width previous).writes
        rw [show (splitOccurrence width previous).writes =
            (splitter width).ports.outputs.labels.values by
          change (splitter width).ports.outputs.allSelection.labels = _
          rw [SignalMap.allSelection_labels]]
        exact ListIndex.get_eq
          ((splitter width).ports.outputs.labels.locate index.castSucc) ▸
            List.get_mem _ _⟩)
    (by simp)
  (.call (decodeOccurrence width previous)
    (by intro port _; cases port; exact ⟨SignalComponentRule.apply, by simp, by
      change AggregatePort.value ∈ [AggregatePort.value]; simp⟩)
    (by simp)
  (.call (invertOccurrence width previous)
    (by intro port _; cases port; exact ⟨SignalComponentRule.apply, by simp, by
      change highIndex width ∈ (splitOccurrence width previous).writes
      rw [show (splitOccurrence width previous).writes =
          (splitter width).ports.outputs.labels.values by
        change (splitter width).ports.outputs.allSelection.labels = _
        rw [SignalMap.allSelection_labels]]
      exact ListIndex.get_eq
        ((splitter width).ports.outputs.labels.locate (highIndex width)) ▸
          List.get_mem _ _⟩)
    (by simp)
  (.call (lowerOccurrence width previous)
    (by intro input _; cases input with
      | value => exact ⟨Rule.apply, by simp, by
          change Output.result ∈ [Output.result]; simp⟩
      | mask => exact ⟨Primitives.NotRule.apply, by simp, by
          change Primitives.SingleOutput.output ∈ [.output]; simp⟩)
    (by simp)
  (.call (upperOccurrence width previous)
    (by intro input _; cases input with
      | value => exact ⟨Rule.apply, by simp, by
          change Output.result ∈ [Output.result]; simp⟩
      | mask => exact ⟨SignalComponentRule.apply, by simp, by
          change highIndex width ∈ (splitOccurrence width previous).writes
          rw [show (splitOccurrence width previous).writes =
              (splitter width).ports.outputs.labels.values by
            change (splitter width).ports.outputs.allSelection.labels = _
            rw [SignalMap.allSelection_labels]]
          exact ListIndex.get_eq
            ((splitter width).ports.outputs.labels.locate (highIndex width)) ▸
              List.get_mem _ _⟩)
    (by simp)
  (.call (concatOccurrence width previous)
    (by intro input _; cases input with
      | left => exact ⟨Modules.Mask.Rule.apply, by simp, by
          change Modules.Mask.Output.result ∈ [Modules.Mask.Output.result]; simp⟩
      | right => exact ⟨Modules.Mask.Rule.apply, by simp, by
          change Modules.Mask.Output.result ∈ [Modules.Mask.Output.result]; simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output
    exact ⟨Modules.VectorConcat.Rule.apply, by simp, by
      change Modules.VectorConcat.Output.result ∈ [.result]; simp⟩))))))))

private def succStateSchedule (width : Nat) (previous : Implementation width) :
    Certified.StateSchedule (succBody width) (succChildren width previous) :=
  .done (by
    intro child input member
    cases child with
    | split | lowerBits =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | decode =>
        change input ∈ (cycleContract width).stateRule.readsInputs.labels at member
        exact nomatch member
    | invert =>
        change input ∈ (CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | lowerMask | upperMask =>
        change input ∈ (Modules.Mask.cycleContract _).stateRule.readsInputs.labels at member
        exact nomatch member
    | concat =>
        change input ∈ (Modules.VectorConcat.cycleContract _ _ _).stateRule.readsInputs.labels at member
        exact nomatch member)

private def succSchedules (width : Nat) (previous : Implementation width) :
    Certified.RuleSchedules (succBody width) (succChildren width previous)
      (cycleContract (width + 1)) where
  output | .apply => succOutputSchedule width previous
  state := succStateSchedule width previous

private theorem succCoversChildren (width : Nat) (previous : Implementation width) :
    (succSchedules width previous).CoversChildren := by
  intro child rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs (succSchedules width previous) .apply
  cases child with
  | split =>
      change SignalComponentRule at rule
      cases rule
      change splitOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | lowerBits =>
      change SignalComponentRule at rule
      cases rule
      change lowerBitsOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | decode =>
      change Rule at rule
      cases rule
      change decodeOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | invert =>
      change Primitives.NotRule at rule
      cases rule
      change invertOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | lowerMask =>
      change Modules.Mask.Rule at rule
      cases rule
      change lowerOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | upperMask =>
      change Modules.Mask.Rule at rule
      cases rule
      change upperOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]
  | concat =>
      change Modules.VectorConcat.Rule at rule
      cases rule
      change concatOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Certified.Schedule.finalAvailability]

private def splitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private noncomputable def lowerBitsInputs (width : Nat) (previous : Implementation width)
    (split : ProposedValues (succChildren width previous .split).moduleStructure) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split.outputs index.castSucc

private noncomputable def decodeInputs (width : Nat) (previous : Implementation width)
    (lowerBits : ProposedValues (succChildren width previous .lowerBits).moduleStructure) :
    (ports width).inputs.Values
  | .value => lowerBits.outputs .value

private noncomputable def invertInputs (width : Nat) (previous : Implementation width)
    (split : ProposedValues (succChildren width previous .split).moduleStructure) :
    Primitives.not.ports.inputs.Values
  | .input => split.outputs (highIndex width)

private noncomputable def lowerInputs (width : Nat) (previous : Implementation width)
    (decoded : ProposedValues (succChildren width previous .decode).moduleStructure)
    (inverted : ProposedValues (succChildren width previous .invert).moduleStructure) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded.outputs .result
  | .mask => inverted.outputs .output

private noncomputable def upperInputs (width : Nat) (previous : Implementation width)
    (split : ProposedValues (succChildren width previous .split).moduleStructure)
    (decoded : ProposedValues (succChildren width previous .decode).moduleStructure) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded.outputs .result
  | .mask => split.outputs (highIndex width)

private noncomputable def concatInputs (width : Nat) (previous : Implementation width)
    (lower : ProposedValues (succChildren width previous .lowerMask).moduleStructure)
    (upper : ProposedValues (succChildren width previous .upperMask).moduleStructure) :
    (Modules.VectorConcat.ports .bit (size width) (size width)).inputs.Values
  | .left => lower.outputs .result
  | .right => upper.outputs .result

private theorem succHasStructuralResult (width : Nat) (previous : Implementation width)
    (inputs : (ports (width + 1)).inputs.Values)
    (state : (Certified.moduleStructure (succBody width)
      (succChildren width previous)).State) :
    ∃ proposal, (Certified.moduleStructure (succBody width)
      (succChildren width previous)).IsSolution inputs state proposal := by
  rcases (succChildren width previous .split).hasStructuralResult
      (splitInputs width inputs) (state .split) with ⟨split, splitSatisfies⟩
  rcases (succChildren width previous .lowerBits).hasStructuralResult
      (lowerBitsInputs width previous split) (state .lowerBits) with
    ⟨lowerBits, lowerBitsSatisfies⟩
  rcases (succChildren width previous .decode).hasStructuralResult
      (decodeInputs width previous lowerBits) (state .decode) with ⟨decoded, decodeSatisfies⟩
  rcases (succChildren width previous .invert).hasStructuralResult
      (invertInputs width previous split) (state .invert) with ⟨inverted, invertSatisfies⟩
  rcases (succChildren width previous .lowerMask).hasStructuralResult
      (lowerInputs width previous decoded inverted) (state .lowerMask) with
    ⟨lower, lowerSatisfies⟩
  rcases (succChildren width previous .upperMask).hasStructuralResult
      (upperInputs width previous split decoded) (state .upperMask) with
    ⟨upper, upperSatisfies⟩
  rcases (succChildren width previous .concat).hasStructuralResult
      (concatInputs width previous lower upper) (state .concat) with
    ⟨concat, concatSatisfies⟩
  let proposals : (child : SuccInstance) →
      ProposedValues (Certified.childStructure (succChildren width previous) child)
    | .split => split
    | .lowerBits => lowerBits
    | .decode => decoded
    | .invert => inverted
    | .lowerMask => lower
    | .upperMask => upper
    | .concat => concat
  let outputs : (ports (width + 1)).outputs.Values := fun
    | .result => concat.outputs .result
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child <;>
      change (succChildren width previous _).moduleStructure.IsSolution
        (ProposedValues.childInputs (succBody width) _ inputs proposals _)
        (state _) _
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .split =
          splitInputs width inputs by funext port; cases port; rfl]
      exact splitSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .lowerBits =
          lowerBitsInputs width previous split by funext index; rfl]
      exact lowerBitsSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .decode =
          decodeInputs width previous lowerBits by funext port; cases port; rfl]
      exact decodeSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .invert =
          invertInputs width previous split by funext port; cases port; rfl]
      exact invertSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .lowerMask =
          lowerInputs width previous decoded inverted by funext port; cases port <;> rfl]
      exact lowerSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .upperMask =
          upperInputs width previous split decoded by funext port; cases port <;> rfl]
      exact upperSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .concat =
          concatInputs width previous lower upper by funext port; cases port <;> rfl]
      exact concatSatisfies

private theorem succImplements (width : Nat) (previous : Implementation width) :
    Implements (Certified.moduleStructure (succBody width)
      (succChildren width previous)) (cycleContract (width + 1))
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childSatisfies := satisfies.2
  have splitOutputs : (proposal.snd .split).outputs =
      (splitter width).outputValues (splitInputs width inputs) :=
    childSatisfies .split
  have lowerOutputs : (proposal.snd .lowerBits).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width) _ inputs proposal.snd .lowerBits) :=
    childSatisfies .lowerBits

  rcases (succChildren width previous .decode).hasCorrespondingState
      (structuralState .decode) with ⟨decodeState, decodeCorresponds⟩
  rcases Certified.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .decode decodeState decodeCorresponds with
    ⟨_, decodeEvaluates, _⟩
  have decodedEquation := (outputRule_holds_iff width _ decodeState _).mp
    (decodeEvaluates.1 Rule.apply)

  rcases (succChildren width previous .invert).hasCorrespondingState
      (structuralState .invert) with ⟨invertState, invertCorresponds⟩
  rcases Certified.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .invert invertState invertCorresponds with
    ⟨_, invertEvaluates, _⟩
  have invertEquation := (Primitives.notOutputRule_holds_iff _ invertState _).mp
    (invertEvaluates.1 Primitives.NotRule.apply)

  rcases (succChildren width previous .lowerMask).hasCorrespondingState
      (structuralState .lowerMask) with ⟨lowerState, lowerCorresponds⟩
  rcases Certified.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .lowerMask lowerState lowerCorresponds with
    ⟨_, lowerEvaluates, _⟩
  have lowerEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ lowerState _).mp
      (lowerEvaluates.1 Modules.Mask.Rule.apply)

  rcases (succChildren width previous .upperMask).hasCorrespondingState
      (structuralState .upperMask) with ⟨upperState, upperCorresponds⟩
  rcases Certified.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .upperMask upperState upperCorresponds with
    ⟨_, upperEvaluates, _⟩
  have upperEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ upperState _).mp
      (upperEvaluates.1 Modules.Mask.Rule.apply)

  rcases (succChildren width previous .concat).hasCorrespondingState
      (structuralState .concat) with ⟨concatState, concatCorresponds⟩
  rcases Certified.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .concat concatState concatCorresponds with
    ⟨_, concatEvaluates, _⟩
  have concatEquation := (Modules.VectorConcat.outputRule_holds_iff
    .bit (size width) (size width) _ concatState _).mp
      (concatEvaluates.1 Modules.VectorConcat.Rule.apply)

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [oneHot_eq_decode]
    change proposal.fst .result = decode (width + 1) (inputs .value)
    rw [show proposal.fst .result =
        (proposal.snd .concat).outputs .result by exact boundary .result]
    have lowerBitsInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .lowerBits =
          lowerBitsInputs width previous (proposal.snd .split) := by
      funext index
      rfl
    have decodeInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .decode =
          decodeInputs width previous (proposal.snd .lowerBits) := by
      funext port; cases port; rfl
    have invertInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .invert =
          invertInputs width previous (proposal.snd .split) := by
      funext port; cases port; rfl
    have lowerInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .lowerMask =
          lowerInputs width previous (proposal.snd .decode)
            (proposal.snd .invert) := by
      funext port; cases port <;> rfl
    have upperInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .upperMask =
          upperInputs width previous (proposal.snd .split)
            (proposal.snd .decode) := by
      funext port; cases port <;> rfl
    have concatInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .concat =
          concatInputs width previous (proposal.snd .lowerMask)
            (proposal.snd .upperMask) := by
      funext port; cases port <;> rfl
    rw [lowerInputsEquation] at lowerEquation
    rw [upperInputsEquation] at upperEquation
    rw [decodeInputsEquation] at decodedEquation
    rw [oneHot_eq_decode] at decodedEquation
    rw [invertInputsEquation] at invertEquation
    rw [lowerBitsInputsEquation] at lowerOutputs
    rw [concatInputsEquation] at concatEquation
    have lowerValue : (proposal.snd .lowerBits).outputs .value =
        fun index => inputs .value index.castSucc := by
      rw [congrFun lowerOutputs .value]
      funext index
      change (proposal.snd .split).outputs index.castSucc = inputs .value index.castSucc
      rw [splitOutputs]
      rfl
    have splitHigh : (proposal.snd .split).outputs (highIndex width) =
        inputs .value (Fin.last width) := by
      rw [splitOutputs]
      rfl
    change (proposal.snd .decode).outputs .result =
      decode width ((proposal.snd .lowerBits).outputs .value) at decodedEquation
    rw [lowerValue] at decodedEquation
    change (proposal.snd .invert).outputs .output =
      !(proposal.snd .split).outputs (highIndex width) at invertEquation
    rw [splitHigh] at invertEquation
    rw [concatEquation]
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro lowerIndex
      rw [Modules.VectorConcat.concat_left]
      change (proposal.snd .lowerMask).outputs .result lowerIndex = _
      rw [congrFun lowerEquation lowerIndex]
      simp [lowerInputs, SignalType.mask]
      rw [congrFun decodedEquation lowerIndex, invertEquation]
      simp [decode, Bool.and_comm]
    · intro upperIndex
      rw [Modules.VectorConcat.concat_right]
      change (proposal.snd .upperMask).outputs .result upperIndex = _
      rw [congrFun upperEquation upperIndex]
      simp [upperInputs, SignalType.mask]
      rw [congrFun decodedEquation upperIndex]
      rw [splitHigh]
      simp only [decode]
      rw [Bool.and_comm (decode width
        (fun index => inputs .value index.castSucc) upperIndex)
          (inputs .value (Fin.last width))]
      symm
      rw [show upperIndex.addNat (size width) =
          Fin.natAdd (size width) upperIndex by
        apply Fin.ext
        simp [Fin.addNat, Fin.natAdd, Nat.add_comm]]
      apply Fin.addCases_right
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private theorem succModuleStructure_eq (width : Nat) (previous : Implementation width) :
    moduleStructure (width + 1) =
      Certified.moduleStructure (succBody width) (succChildren width previous) := by
  change ModuleStructure.composite (succBody width) (fun
    | .split => (splitter width).certified.moduleStructure
    | .lowerBits => (lowerCombiner width).certified.moduleStructure
    | .decode => moduleStructure width
    | .invert => Primitives.notCertified.moduleStructure
    | .lowerMask | .upperMask =>
        Modules.Mask.moduleStructure (.vector (size width) .bit)
    | .concat => Modules.VectorConcat.moduleStructure .bit (size width) (size width)) = _
  unfold Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

private def succImplementation (width : Nat) (previous : Implementation width) :
    Implementation (width + 1) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := by
    rw [succModuleStructure_eq width previous]
    exact succHasStructuralResult width previous
  structuralResultUnique := by
    rw [succModuleStructure_eq width previous]
    exact (succSchedules width previous).hasAtMostOneSolution
      (succCoversChildren width previous)
  implements := by
    rw [succModuleStructure_eq width previous]
    exact succImplements width previous

noncomputable def implementation : (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementation width)

noncomputable def certification (width : Nat) :
    ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) : ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Silean2.Modules.BinaryToOneHot

namespace Silean2.Modules.BinaryToOneHot.Naming

open Silean2 Silean2.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.BinaryToOneHot.ports width) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => .vector .bit
  outputTypes := fun | .result => .vector .bit

def naming : (width : Nat) →
    ModuleNaming (Modules.BinaryToOneHot.moduleStructure width)
  | 0 => by
      rw [Modules.BinaryToOneHot.moduleStructure.eq_def]
      exact .composite ⟨"binary_to_one_hot", "base", []⟩ (ports 0)
        (fun | Modules.BinaryToOneHot.BaseInstance.constant => "constant")
        (fun
          | Modules.BinaryToOneHot.BaseInstance.constant =>
              Modules.Constant.Naming.naming (SignalType.vector 1 .bit)
                Modules.BinaryToOneHot.baseValue)
  | width + 1 => by
      rw [Modules.BinaryToOneHot.moduleStructure.eq_def]
      exact .composite
        ⟨"binary_to_one_hot", "recursive", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .split => "split"
          | .lowerBits => "lower_bits"
          | .decode => "decode_lower"
          | .invert => "invert_high"
          | .lowerMask => "lower_mask"
          | .upperMask => "upper_mask"
          | .concat => "concat")
        (fun
          | .split => Silean2.Naming.SignalAdapter.splitter
              (Modules.BinaryToOneHot.splitter width)
          | .lowerBits => Silean2.Naming.SignalAdapter.combiner
              (Modules.BinaryToOneHot.lowerCombiner width)
          | .decode => naming width
          | .invert => Silean2.Naming.Primitive.not
          | .lowerMask | .upperMask => Modules.Mask.Naming.naming
              (.vector (Modules.BinaryToOneHot.size width) .bit)
          | .concat => Modules.VectorConcat.Naming.naming .bit
              (Modules.BinaryToOneHot.size width) (Modules.BinaryToOneHot.size width))

def namedModule (width : Nat) : NamedModule where
  ports := Modules.BinaryToOneHot.ports width
  moduleStructure := Modules.BinaryToOneHot.moduleStructure width
  naming := naming width

end Silean2.Modules.BinaryToOneHot.Naming
