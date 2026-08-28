import Silean.Contracts.Cycle.CycleSchedule
import Silean.Foundation.BitVector
import Silean.Modules.Constant
import Silean.Modules.HalfAdder
import Silean.Modules.VectorConcat
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Increment

open Silean

/-! A wrapping combinational incrementer for an LSB-first vector of bits. -/

inductive Input | value
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun | .value => .vector width .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .result => .vector width .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

/-! Add one carry bit to an LSB-first vector. Recursion removes the highest
indexed bit, so the recursive call computes the carry arriving from all lower
indices before the high bit is evaluated. -/
private def addCarry : (width : Nat) → (Fin width → Bool) → Bool →
    (Fin width → Bool) × Bool
  | 0, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, bits, carry =>
      let lower := addCarry width (fun index => bits index.castSucc) carry
      let high := HalfAdder.sumValue (bits (Fin.last width)) lower.2
      let carryOut := HalfAdder.carryValue (bits (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

def incrementValue (width : Nat) (bits : Fin width → Bool) : Fin width → Bool :=
  (addCarry width bits true).1

@[simp] private theorem toNat_lastCases (width : Nat) (high : Bool)
    (lower : Fin width → Bool) :
    BitVector.toNat (width + 1) (Fin.lastCases high lower) =
      (if high then BitVector.cardinality width else 0) +
        BitVector.toNat width lower := by
  simp [BitVector.toNat]

private theorem addCarry_numeric : ∀ (width : Nat) (bits : Fin width → Bool)
    (carry : Bool),
    BitVector.toNat width (addCarry width bits carry).1 +
        BitVector.cardinality width * (addCarry width bits carry).2.toNat =
      BitVector.toNat width bits + carry.toNat
  | 0, _, carry => by simp [addCarry, BitVector.toNat, BitVector.cardinality]
  | width + 1, bits, carry => by
      have lower := addCarry_numeric width
        (fun index => bits index.castSucc) carry
      have cardinalityPositive : 0 < BitVector.cardinality width := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.pow_pos (by omega)
      rw [BitVector.cardinality_eq_pow] at lower cardinalityPositive ⊢
      have lowerResultEta :
          (fun index => (addCarry width
            (fun index => bits index.castSucc) carry).1 index) =
          (addCarry width (fun index => bits index.castSucc) carry).1 := rfl
      cases highValue : bits (Fin.last width) <;>
        cases lowerCarry : (addCarry width
          (fun index => bits index.castSucc) carry).2 <;>
        simp [addCarry, BitVector.toNat,
          highValue, lowerCarry, lowerResultEta,
          HalfAdder.sumValue, HalfAdder.carryValue,
          Primitives.xorValue] at lower ⊢ <;>
        omega

theorem incrementValue_toNat (width : Nat) (bits : Fin width → Bool) :
    BitVector.toNat width (incrementValue width bits) =
      (BitVector.toNat width bits + 1) % BitVector.cardinality width := by
  have equation := addCarry_numeric width bits true
  simp at equation
  have bound := BitVector.toNat_lt_cardinality width (incrementValue width bits)
  have bound' : BitVector.toNat width (addCarry width bits true).1 < 2 ^ width := by
    simpa [incrementValue, BitVector.cardinality_eq_pow] using bound
  change BitVector.toNat width (addCarry width bits true).1 = _
  rw [← equation]
  simp [Nat.mod_eq_of_lt bound']

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap
      { inputTypes := .cons (.vector width .bit) .nil
        outputTypes := .cons (.vector width .bit) .nil } where
  readsInputs := (inputMap width).select .value
  writesOutputs := (outputMap width).select .result
  target | (value, ()), _ => (incrementValue width value, ())

@[reducible] def cycleContract (width : Nat) : Contracts.Cycle.ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule width⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = incrementValue width (inputs .value) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

theorem result_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .result = incrementValue width (inputs .value) :=
  (outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)

theorem result_toNat_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs) :
    BitVector.toNat width (outputs .result) =
      (BitVector.toNat width (inputs .value) + 1) % BitVector.cardinality width := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]
  exact incrementValue_toNat width (inputs .value)

theorem result_toNat_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    BitVector.toNat width (outputs .result) =
      (BitVector.toNat width (inputs .value) + 1) % BitVector.cardinality width := by
  exact result_toNat_of_holds width inputs state outputs (evaluates.1 .apply)

/-! `Ripple` is the implementation-only recursive component used by Increment. It
adds an explicit carry input and returns both the vector result and carry out.
The public Increment module below fixes that input to true and hides carry out. -/
namespace Ripple

private inductive Input | value | carryIn
deriving Enumeration

private inductive Output | result | carryOut
deriving Enumeration

@[reducible] private def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector width .bit
    | .carryIn => .bit

@[reducible] private def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector width .bit
    | .carryOut => .bit

@[reducible] private def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

private inductive Rule | apply
deriving Enumeration

private def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap
      { inputTypes := .cons (.vector width .bit) (.cons .bit .nil)
        outputTypes := .cons (.vector width .bit) (.cons .bit .nil) } where
  readsInputs := (inputMap width).select .carryIn |>.prepend .value
  writesOutputs := (outputMap width).select .carryOut |>.prepend .result
  target := fun
    | (value, (carry, ())), _ =>
        ((addCarry width value carry).1, ((addCarry width value carry).2, ()))

@[reducible] private def cycleContract (width : Nat) : Contracts.Cycle.ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule width⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] private theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = (addCarry width (inputs .value) (inputs .carryIn)).1 ∧
      outputs .carryOut = (addCarry width (inputs .value) (inputs .carryIn)).2 := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

private def emptyValue : (SignalType.vector 0 .bit).Denote :=
  fun index => Fin.elim0 index

private inductive BaseInstance | empty
deriving Enumeration

@[reducible] private def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .empty => Modules.Constant.ports (.vector 0 .bit)

@[reducible] private def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

private def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput
    | .result => baseContext.instanceOutput .empty .output
    | .carryOut => baseContext.moduleInput .carryIn
  instanceInput | .empty, impossible => nomatch impossible

@[reducible] private def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

private def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .empty => Modules.Constant.moduleStructure (.vector 0 .bit) emptyValue

private def splitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
private def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
private def highCombiner : Composition.SignalCombiner := .vector 1 .bit
private def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

private inductive SuccInstance
  | split
  | lowerBits
  | lowerRipple
  | highAdder
  | highBit
  | concat
deriving Enumeration

@[reducible] private def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .lowerRipple => ports width
    | .highAdder => HalfAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] private def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

private def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    | .result => (succContext width).instanceOutput .concat .result
    | .carryOut => (succContext width).instanceOutput .highAdder .carry
  instanceInput
    | .split, .value => (succContext width).moduleInput .value
    | .lowerBits, index =>
        (succContext width).instanceOutput .split index.castSucc
    | .lowerRipple, .value =>
        (succContext width).instanceOutput .lowerBits .value
    | .lowerRipple, .carryIn => (succContext width).moduleInput .carryIn
    | .highAdder, .left =>
        (succContext width).instanceOutput .split (highIndex width)
    | .highAdder, .right =>
        (succContext width).instanceOutput .lowerRipple .carryOut
    | .highBit, _ => (succContext width).instanceOutput .highAdder .sum
    | .concat, .left =>
        (succContext width).instanceOutput .lowerRipple .result
    | .concat, .right => (succContext width).instanceOutput .highBit .value

@[reducible] private def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

private def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .split => (splitter width).certified.moduleStructure
      | .lowerBits => (lowerCombiner width).certified.moduleStructure
      | .lowerRipple => moduleStructure width
      | .highAdder => HalfAdder.moduleStructure
      | .highBit => highCombiner.certified.moduleStructure
      | .concat => VectorConcat.moduleStructure .bit width 1

private abbrev Implementation (width : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private noncomputable def baseChildren : Contracts.Cycle.Certification.Children baseBody
  | .empty => Modules.Constant.certified (.vector 0 .bit) emptyValue

private abbrev baseOccurrence : Contracts.Cycle.Certification.RuleOccurrence baseChildren :=
  ⟨.empty, Primitives.ConstantRule.apply⟩

private def baseOutputSchedule : Contracts.Cycle.Certification.OutputSchedule baseBody baseChildren
    (cycleContract 0) .apply :=
  .call baseOccurrence
    (by intro input member; exact nomatch input)
    (by simp)
    (.done (by
      intro output _
      cases output with
      | result => exact ⟨Primitives.ConstantRule.apply, by simp, by
          change Primitives.SingleOutput.output ∈ [.output]
          simp⟩
      | carryOut =>
          simp [cycleContract, outputRule, SignalSelection.labels,
            SignalSelection.prepend, SignalMap.select, Contracts.Cycle.Certification.sourceAvailable,
            baseBody, baseWiring, baseContext, EndpointContext.moduleInput]))

private def baseStateSchedule : Contracts.Cycle.Certification.StateSchedule baseBody baseChildren :=
  .done (by
    intro child input member
    cases child
    change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
    exact nomatch member)

private def baseSchedules : Contracts.Cycle.Certification.RuleSchedules baseBody baseChildren
    (cycleContract 0) where
  output | .apply => baseOutputSchedule
  state := baseStateSchedule

private theorem baseCoversChildren : baseSchedules.CoversChildren := by
  intro child rule
  cases child
  change Primitives.ConstantRule at rule
  cases rule
  apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
  apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs baseSchedules .apply
  change baseOccurrence ∈ baseOutputSchedule.finalAvailability
  simp [baseOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private def baseChildInputs :
    (Modules.Constant.ports (.vector 0 .bit)).inputs.Values :=
  fun impossible => nomatch impossible

private theorem baseHasStructuralResult (inputs : (ports 0).inputs.Values)
    (state : baseModuleStructure.State) :
    ∃ proposal, baseModuleStructure.IsSolution inputs state proposal := by
  rcases (baseChildren .empty).hasStructuralResult baseChildInputs
      (state .empty) with ⟨empty, emptySatisfies⟩
  let children : (child : BaseInstance) →
      ProposedValues (Contracts.Cycle.Certification.childStructure baseChildren child)
    | .empty => empty
  let outputs : (ports 0).outputs.Values := fun
    | .result => empty.outputs .output
    | .carryOut => inputs .carryIn
  refine ⟨ProposedValues.composite outputs children, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child
    change (baseChildren .empty).moduleStructure.IsSolution
      (ProposedValues.childInputs baseBody _ inputs children .empty)
      (state .empty) empty
    rw [show ProposedValues.childInputs baseBody _ inputs children .empty =
        baseChildInputs by funext impossible; exact nomatch impossible]
    exact emptySatisfies

private theorem baseImplements : Contracts.Cycle.Implements baseModuleStructure
    (cycleContract 0) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · funext index
      exact Fin.elim0 index
    · rw [show proposal.outputs .carryOut = inputs .carryIn by
          exact boundary .carryOut]
      rfl
  · rfl

private def baseImplementation : Implementation 0 where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := baseHasStructuralResult
  structuralResultUnique := baseSchedules.hasAtMostOneSolution baseCoversChildren
  implements := baseImplements

@[reducible] private noncomputable def succChildren (width : Nat)
    (previous : Implementation width) : Contracts.Cycle.Certification.Children (succBody width)
  | .split => (splitter width).certified
  | .lowerBits => (lowerCombiner width).certified
  | .lowerRipple => previous.certified
  | .highAdder => HalfAdder.certified
  | .highBit => highCombiner.certified
  | .concat => VectorConcat.certified .bit width 1

private abbrev splitOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.lowerBits, Composition.SignalComponentRule.apply⟩
private abbrev lowerRippleOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.lowerRipple, Rule.apply⟩
private abbrev highSumOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.highAdder, HalfAdder.Rule.sum⟩
private abbrev highCarryOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.highAdder, HalfAdder.Rule.carry⟩
private abbrev highBitOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.highBit, Composition.SignalComponentRule.apply⟩
private abbrev concatOccurrence (width) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleOccurrence (succChildren width previous) :=
  ⟨.concat, VectorConcat.Rule.apply⟩

private theorem splitWrites (width : Nat) (previous : Implementation width)
    (index : (splitter width).ports.outputs.Label) :
    index ∈ (splitOccurrence width previous).writes := by
  change index ∈ (splitter width).ports.outputs.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact ListIndex.get_eq ((splitter width).ports.outputs.labels.locate index) ▸
    List.get_mem _ _

private def succOutputSchedule (width : Nat) (previous : Implementation width) :
    Contracts.Cycle.Certification.OutputSchedule (succBody width) (succChildren width previous)
      (cycleContract (width + 1)) .apply :=
  .call (splitOccurrence width previous)
    (by
      intro input _
      cases input
      simp [cycleContract, outputRule, SignalMap.select,
        SignalSelection.labels, SignalSelection.prepend,
        Contracts.Cycle.Certification.sourceAvailable, succBody, succWiring, succContext,
        EndpointContext.moduleInput])
    (by simp)
  (.call (lowerBitsOccurrence width previous)
    (by intro index _; exact ⟨Composition.SignalComponentRule.apply, by simp,
      splitWrites width previous index.castSucc⟩)
    (by simp)
  (.call (lowerRippleOccurrence width previous)
    (by
      intro input _
      cases input with
      | value => exact ⟨Composition.SignalComponentRule.apply, by simp, by
          change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]
          simp⟩
      | carryIn =>
          simp [cycleContract, outputRule, SignalMap.select,
            SignalSelection.labels, SignalSelection.prepend,
            Contracts.Cycle.Certification.sourceAvailable, succBody, succWiring, succContext,
            EndpointContext.moduleInput])
    (by simp)
  (.call (highSumOccurrence width previous)
    (by
      intro input _
      cases input with
      | left => exact ⟨Composition.SignalComponentRule.apply, by simp,
          splitWrites width previous (highIndex width)⟩
      | right => exact ⟨Rule.apply, by simp, by
          change Output.carryOut ∈ [Output.result, Output.carryOut]
          simp⟩)
    (by simp)
  (.call (highCarryOccurrence width previous)
    (by
      intro input _
      cases input with
      | left => exact ⟨Composition.SignalComponentRule.apply, by simp,
          splitWrites width previous (highIndex width)⟩
      | right => exact ⟨Rule.apply, by simp, by
          change Output.carryOut ∈ [Output.result, Output.carryOut]
          simp⟩)
    (by simp)
  (.call (highBitOccurrence width previous)
    (by intro index _; exact ⟨HalfAdder.Rule.sum, by simp, by
      change HalfAdder.Output.sum ∈ [HalfAdder.Output.sum]
      simp⟩)
    (by simp)
  (.call (concatOccurrence width previous)
    (by
      intro input _
      cases input with
      | left => exact ⟨Rule.apply, by simp, by
          change Output.result ∈ [Output.result, Output.carryOut]
          simp⟩
      | right => exact ⟨Composition.SignalComponentRule.apply, by simp, by
          change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]
          simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output with
    | result => exact ⟨VectorConcat.Rule.apply, by simp, by
        change VectorConcat.Output.result ∈ [VectorConcat.Output.result]
        simp⟩
    | carryOut => exact ⟨HalfAdder.Rule.carry, by simp, by
        change HalfAdder.Output.carry ∈ [HalfAdder.Output.carry]
        simp⟩))))))))

private def succStateSchedule (width : Nat) (previous : Implementation width) :
    Contracts.Cycle.Certification.StateSchedule (succBody width) (succChildren width previous) :=
  .done (by
    intro child input member
    cases child with
    | split | lowerBits | highBit =>
        change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | lowerRipple =>
        change input ∈ (cycleContract width).stateRule.readsInputs.labels at member
        exact nomatch member
    | highAdder =>
        change input ∈ HalfAdder.cycleContract.stateRule.readsInputs.labels at member
        exact nomatch member
    | concat =>
        change input ∈ (VectorConcat.cycleContract .bit width 1).stateRule.readsInputs.labels
          at member
        exact nomatch member)

private def succSchedules (width : Nat) (previous : Implementation width) :
    Contracts.Cycle.Certification.RuleSchedules (succBody width) (succChildren width previous)
      (cycleContract (width + 1)) where
  output | .apply => succOutputSchedule width previous
  state := succStateSchedule width previous

private theorem succCoversChildren (width : Nat) (previous : Implementation width) :
    (succSchedules width previous).CoversChildren := by
  intro child rule
  apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
  apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs (succSchedules width previous) .apply
  cases child with
  | split =>
      change Composition.SignalComponentRule at rule; cases rule
      change splitOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | lowerBits =>
      change Composition.SignalComponentRule at rule; cases rule
      change lowerBitsOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | lowerRipple =>
      change Rule at rule; cases rule
      change lowerRippleOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | highAdder =>
      change HalfAdder.Rule at rule
      cases rule with
      | sum =>
          change highSumOccurrence width previous ∈
            (succOutputSchedule width previous).finalAvailability
          simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
      | carry =>
          change highCarryOccurrence width previous ∈
            (succOutputSchedule width previous).finalAvailability
          simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | highBit =>
      change Composition.SignalComponentRule at rule; cases rule
      change highBitOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | concat =>
      change VectorConcat.Rule at rule; cases rule
      change concatOccurrence width previous ∈
        (succOutputSchedule width previous).finalAvailability
      simp [succOutputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private def splitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private noncomputable def lowerBitsInputs (width : Nat)
    (previous : Implementation width)
    (split : ProposedValues (succChildren width previous .split).moduleStructure) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split.outputs index.castSucc

private noncomputable def lowerRippleInputs (width : Nat)
    (previous : Implementation width) (inputs : (ports (width + 1)).inputs.Values)
    (lowerBits : ProposedValues
      (succChildren width previous .lowerBits).moduleStructure) :
    (ports width).inputs.Values
  | .value => lowerBits.outputs .value
  | .carryIn => inputs .carryIn

private noncomputable def highAdderInputs (width : Nat)
    (previous : Implementation width)
    (split : ProposedValues (succChildren width previous .split).moduleStructure)
    (lower : ProposedValues
      (succChildren width previous .lowerRipple).moduleStructure) :
    HalfAdder.ports.inputs.Values
  | .left => split.outputs (highIndex width)
  | .right => lower.outputs .carryOut

private noncomputable def highBitInputs (width : Nat)
    (previous : Implementation width)
    (adder : ProposedValues (succChildren width previous .highAdder).moduleStructure) :
    highCombiner.ports.inputs.Values := fun _ => adder.outputs .sum

private noncomputable def concatInputs (width : Nat)
    (previous : Implementation width)
    (lower : ProposedValues
      (succChildren width previous .lowerRipple).moduleStructure)
    (highBit : ProposedValues (succChildren width previous .highBit).moduleStructure) :
    (VectorConcat.ports .bit width 1).inputs.Values
  | .left => lower.outputs .result
  | .right => highBit.outputs .value

private theorem concat_single_eq_lastCases (lower : Fin width → Bool) (high : Bool) :
    VectorConcat.concat lower (fun _ : Fin 1 => high) =
      Fin.lastCases high lower := by
  funext index
  refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        (Fin.last width) = high := by
      rw [show Fin.last width = Fin.natAdd width (0 : Fin 1) by
        apply Fin.ext; simp]
      exact VectorConcat.concat_right lower (fun _ : Fin 1 => high) 0
    simpa using left
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        lowerIndex.castSucc = lower lowerIndex := by
      rw [show lowerIndex.castSucc = Fin.castAdd 1 lowerIndex by
        apply Fin.ext; rfl]
      exact VectorConcat.concat_left lower (fun _ : Fin 1 => high) lowerIndex
    simpa using left

private theorem succHasStructuralResult (width : Nat) (previous : Implementation width)
    (inputs : (ports (width + 1)).inputs.Values)
    (state : (Contracts.Cycle.Certification.moduleStructure (succBody width)
      (succChildren width previous)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (succBody width)
      (succChildren width previous)).IsSolution inputs state proposal := by
  rcases (succChildren width previous .split).hasStructuralResult
      (splitInputs width inputs) (state .split) with ⟨split, splitSatisfies⟩
  rcases (succChildren width previous .lowerBits).hasStructuralResult
      (lowerBitsInputs width previous split) (state .lowerBits) with
    ⟨lowerBits, lowerBitsSatisfies⟩
  rcases (succChildren width previous .lowerRipple).hasStructuralResult
      (lowerRippleInputs width previous inputs lowerBits) (state .lowerRipple) with
    ⟨lower, lowerSatisfies⟩
  rcases (succChildren width previous .highAdder).hasStructuralResult
      (highAdderInputs width previous split lower) (state .highAdder) with
    ⟨adder, adderSatisfies⟩
  rcases (succChildren width previous .highBit).hasStructuralResult
      (highBitInputs width previous adder) (state .highBit) with
    ⟨highBit, highBitSatisfies⟩
  rcases (succChildren width previous .concat).hasStructuralResult
      (concatInputs width previous lower highBit) (state .concat) with
    ⟨concat, concatSatisfies⟩
  let proposals : (child : SuccInstance) →
      ProposedValues (Contracts.Cycle.Certification.childStructure (succChildren width previous) child)
    | .split => split
    | .lowerBits => lowerBits
    | .lowerRipple => lower
    | .highAdder => adder
    | .highBit => highBit
    | .concat => concat
  let outputs : (ports (width + 1)).outputs.Values := fun
    | .result => concat.outputs .result
    | .carryOut => adder.outputs .carry
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
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
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .lowerRipple =
          lowerRippleInputs width previous inputs lowerBits by
            funext port; cases port <;> rfl]
      exact lowerSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .highAdder =
          highAdderInputs width previous split lower by
            funext port; cases port <;> rfl]
      exact adderSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .highBit =
          highBitInputs width previous adder by funext index; rfl]
      exact highBitSatisfies
    · rw [show ProposedValues.childInputs (succBody width) _ inputs proposals .concat =
          concatInputs width previous lower highBit by
            funext port; cases port <;> rfl]
      exact concatSatisfies

private theorem succImplements (width : Nat) (previous : Implementation width) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (succBody width)
      (succChildren width previous)) (cycleContract (width + 1))
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childSatisfies := satisfies.2
  have splitOutputs : (proposal.2 .split).outputs =
      (splitter width).outputValues (splitInputs width inputs) :=
    childSatisfies .split
  have lowerBitsOutputs : (proposal.2 .lowerBits).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width) _ inputs proposal.2 .lowerBits) :=
    childSatisfies .lowerBits
  have highBitOutputs : (proposal.2 .highBit).outputs =
      highCombiner.outputValues
        (ProposedValues.childInputs (succBody width) _ inputs proposal.2 .highBit) :=
    childSatisfies .highBit

  rcases (succChildren width previous .lowerRipple).hasCorrespondingState
      (structuralState .lowerRipple) with ⟨lowerState, lowerCorresponds⟩
  rcases Contracts.Cycle.Certification.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .lowerRipple lowerState lowerCorresponds with
    ⟨_, lowerEvaluates, _⟩
  have lowerEquation := (outputRule_holds_iff width _ lowerState _).mp
    (lowerEvaluates.1 Rule.apply)

  rcases (succChildren width previous .highAdder).hasCorrespondingState
      (structuralState .highAdder) with ⟨adderState, adderCorresponds⟩
  rcases Contracts.Cycle.Certification.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .highAdder adderState adderCorresponds with
    ⟨_, adderEvaluates, _⟩
  have sumEquation := HalfAdder.sum_of_evaluatesTo _ adderState _ _ adderEvaluates
  have carryEquation := HalfAdder.carry_of_evaluatesTo _ adderState _ _ adderEvaluates

  rcases (succChildren width previous .concat).hasCorrespondingState
      (structuralState .concat) with ⟨concatState, concatCorresponds⟩
  rcases Contracts.Cycle.Certification.childImplements (succChildren width previous) inputs
      structuralState proposal satisfies .concat concatState concatCorresponds with
    ⟨_, concatEvaluates, _⟩
  have concatEquation := (VectorConcat.outputRule_holds_iff .bit width 1
    _ concatState _).mp (concatEvaluates.1 VectorConcat.Rule.apply)

  have lowerBitsInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerBits =
        lowerBitsInputs width previous (proposal.2 .split) := by
    funext index; rfl
  have lowerRippleInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerRipple =
        lowerRippleInputs width previous inputs (proposal.2 .lowerBits) := by
    funext port; cases port <;> rfl
  have highAdderInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highAdder =
        highAdderInputs width previous (proposal.2 .split)
          (proposal.2 .lowerRipple) := by
    funext port; cases port <;> rfl
  have highBitInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highBit =
        highBitInputs width previous (proposal.2 .highAdder) := by
    funext index; rfl
  have concatInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .concat =
        concatInputs width previous (proposal.2 .lowerRipple)
          (proposal.2 .highBit) := by
    funext port; cases port <;> rfl

  rw [lowerBitsInputsEquation] at lowerBitsOutputs
  rw [lowerRippleInputsEquation] at lowerEquation
  rw [highAdderInputsEquation] at sumEquation carryEquation
  rw [highBitInputsEquation] at highBitOutputs
  rw [concatInputsEquation] at concatEquation

  have lowerValue : (proposal.2 .lowerBits).outputs .value =
      fun index => inputs .value index.castSucc := by
    rw [congrFun lowerBitsOutputs .value]
    funext index
    change (proposal.2 .split).outputs index.castSucc = inputs .value index.castSucc
    rw [splitOutputs]
    rfl
  have highValue : (proposal.2 .split).outputs (highIndex width) =
      inputs .value (Fin.last width) := by
    rw [splitOutputs]
    rfl
  have highBitValue : (proposal.2 .highBit).outputs .value =
      fun _ => (proposal.2 .highAdder).outputs .sum := by
    rw [congrFun highBitOutputs .value]
    rfl

  have lowerResultEquation := lowerEquation.1
  change (proposal.2 .lowerRipple).outputs .result =
    (addCarry width ((proposal.2 .lowerBits).outputs .value) (inputs .carryIn)).1
      at lowerResultEquation
  rw [lowerValue] at lowerResultEquation
  have lowerCarryEquation := lowerEquation.2
  change (proposal.2 .lowerRipple).outputs .carryOut =
    (addCarry width ((proposal.2 .lowerBits).outputs .value) (inputs .carryIn)).2
      at lowerCarryEquation
  rw [lowerValue] at lowerCarryEquation
  change (proposal.2 .highAdder).outputs .sum = HalfAdder.sumValue
    ((proposal.2 .split).outputs (highIndex width))
    ((proposal.2 .lowerRipple).outputs .carryOut) at sumEquation
  change (proposal.2 .highAdder).outputs .carry = HalfAdder.carryValue
    ((proposal.2 .split).outputs (highIndex width))
    ((proposal.2 .lowerRipple).outputs .carryOut) at carryEquation
  rw [highValue] at sumEquation carryEquation
  rw [lowerCarryEquation] at sumEquation carryEquation
  change (proposal.2 .concat).outputs .result = VectorConcat.concat
    ((proposal.2 .lowerRipple).outputs .result)
    ((proposal.2 .highBit).outputs .value) at concatEquation
  rw [highBitValue] at concatEquation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · rw [show proposal.outputs .result =
          (proposal.2 .concat).outputs .result by exact boundary .result]
      rw [concatEquation]
      change VectorConcat.concat ((proposal.2 .lowerRipple).outputs .result)
          (fun _ => (proposal.2 .highAdder).outputs .sum) = _
      rw [lowerResultEquation, sumEquation]
      exact concat_single_eq_lastCases _ _
    · change proposal.fst .carryOut = _
      rw [boundary .carryOut]
      change (proposal.2 .highAdder).outputs .carry = _
      rw [carryEquation]
      rfl
  · funext label
    exact nomatch label

private theorem succModuleStructure_eq (width : Nat) (previous : Implementation width) :
    moduleStructure (width + 1) =
      Contracts.Cycle.Certification.moduleStructure (succBody width) (succChildren width previous) := by
  change ModuleStructure.composite (succBody width) (fun
    | .split => (splitter width).certified.moduleStructure
    | .lowerBits => (lowerCombiner width).certified.moduleStructure
    | .lowerRipple => moduleStructure width
    | .highAdder => HalfAdder.moduleStructure
    | .highBit => highCombiner.certified.moduleStructure
    | .concat => VectorConcat.moduleStructure .bit width 1) = _
  unfold Contracts.Cycle.Certification.moduleStructure
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

private noncomputable def implementationDefinition : (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementationDefinition width)

private noncomputable opaque implementation (width : Nat) : Implementation width :=
  implementationDefinition width

private noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

private noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Ripple

/-! ## Public hardware structure

The public incrementer supplies a constant carry-in of one to the recursive
ripple implementation. -/

private inductive Instance
  /-- Supplies the asserted carry-in. -/
  | one
  /-- Propagates that carry through the input bits. -/
  | ripple
deriving Enumeration

@[reducible] private def instancePorts (width : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .one => Modules.Constant.ports .bit
    | .ripple => Ripple.ports width

@[reducible] private def context (width : Nat) : EndpointContext where
  ports := ports width
  instancePorts := instancePorts width

private def wiring (width : Nat) :
    Wiring (context width).ports (context width).instancePorts :=
  let c := context width
  { moduleOutput := fun
    -- The ripple result is the incremented vector.
    | .result => c.instanceOutput .ripple .result
    instanceInput := fun
    | .one, impossible => nomatch impossible
    -- Apply the constant one as the initial carry.
    | .ripple, .value => c.moduleInput .value
    | .ripple, .carryIn => c.instanceOutput .one .output }

@[reducible] private def body (width : Nat) : ModuleBody :=
  ⟨context width, wiring width⟩

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  .composite (body width) fun
    | .one => Modules.Constant.moduleStructure .bit true
    | .ripple => Ripple.moduleStructure width

@[reducible] private noncomputable def children (width : Nat) :
    Contracts.Cycle.Certification.Children (body width)
  | .one => Modules.Constant.certified .bit true
  | .ripple => Ripple.certified width

private abbrev oneOccurrence (width : Nat) :
    Contracts.Cycle.Certification.RuleOccurrence (children width) :=
  ⟨.one, Primitives.ConstantRule.apply⟩

private abbrev rippleOccurrence (width : Nat) :
    Contracts.Cycle.Certification.RuleOccurrence (children width) :=
  ⟨.ripple, Ripple.Rule.apply⟩

private def outputSchedule (width : Nat) :
    Contracts.Cycle.Certification.OutputSchedule (body width) (children width) (cycleContract width) .apply :=
  .call (oneOccurrence width)
    (by intro input member; exact nomatch input)
    (by simp)
  (.call (rippleOccurrence width)
    (by
      intro input _
      cases input with
      | value =>
          simp [cycleContract, outputRule, SignalMap.select,
            SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | carryIn => exact ⟨Primitives.ConstantRule.apply, by simp, by
          change Primitives.SingleOutput.output ∈ [Primitives.SingleOutput.output]
          simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output
    exact ⟨Ripple.Rule.apply, by simp, by
      change Ripple.Output.result ∈ [Ripple.Output.result, Ripple.Output.carryOut]
      simp⟩)))

private def stateSchedule (width : Nat) :
    Contracts.Cycle.Certification.StateSchedule (body width) (children width) :=
  .done (by
    intro child input member
    cases child with
    | one =>
        change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | ripple =>
        change input ∈ (Ripple.cycleContract width).stateRule.readsInputs.labels at member
        exact nomatch member)

private def schedules (width : Nat) :
    Contracts.Cycle.Certification.RuleSchedules (body width) (children width) (cycleContract width) where
  output | .apply => outputSchedule width
  state := stateSchedule width

private theorem coversChildren (width : Nat) : (schedules width).CoversChildren := by
  intro child rule
  apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
  apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs (schedules width) .apply
  cases child with
  | one =>
      change Primitives.ConstantRule at rule; cases rule
      change oneOccurrence width ∈ (outputSchedule width).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | ripple =>
      change Ripple.Rule at rule; cases rule
      change rippleOccurrence width ∈ (outputSchedule width).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private def oneInputs : (Modules.Constant.ports .bit).inputs.Values :=
  fun impossible => nomatch impossible

private noncomputable def rippleInputs (width : Nat)
    (inputs : (ports width).inputs.Values)
    (one : ProposedValues (children width .one).moduleStructure) :
    (Ripple.ports width).inputs.Values
  | .value => inputs .value
  | .carryIn => one.outputs .output

private theorem moduleStructure_eq (width : Nat) :
    moduleStructure width = Contracts.Cycle.Certification.moduleStructure (body width) (children width) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

private theorem compositeHasStructuralResult (width : Nat)
    (inputs : (ports width).inputs.Values)
    (state : (Contracts.Cycle.Certification.moduleStructure (body width) (children width)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (body width) (children width)).IsSolution
      inputs state proposal := by
  rcases (children width .one).hasStructuralResult oneInputs (state .one) with
    ⟨one, oneSatisfies⟩
  rcases (children width .ripple).hasStructuralResult
      (rippleInputs width inputs one) (state .ripple) with
    ⟨ripple, rippleSatisfies⟩
  let proposals : (child : Instance) →
      ProposedValues (Contracts.Cycle.Certification.childStructure (children width) child)
    | .one => one
    | .ripple => ripple
  let outputs : (ports width).outputs.Values := fun
    | .result => ripple.outputs .result
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | one =>
        change (children width .one).moduleStructure.IsSolution
          (ProposedValues.childInputs (body width) _ inputs proposals .one)
          (state .one) one
        rw [show ProposedValues.childInputs (body width) _ inputs proposals .one =
            oneInputs by funext impossible; exact nomatch impossible]
        exact oneSatisfies
    | ripple =>
        change (children width .ripple).moduleStructure.IsSolution
          (ProposedValues.childInputs (body width) _ inputs proposals .ripple)
          (state .ripple) ripple
        rw [show ProposedValues.childInputs (body width) _ inputs proposals .ripple =
            rippleInputs width inputs one by funext port; cases port <;> rfl]
        exact rippleSatisfies

private theorem compositeImplements (width : Nat) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body width) (children width))
    (cycleContract width) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  rcases (children width .one).hasCorrespondingState
      (structuralState .one) with ⟨oneState, oneCorresponds⟩
  rcases Contracts.Cycle.Certification.childImplements (children width) inputs structuralState proposal
      satisfies .one oneState oneCorresponds with ⟨_, oneEvaluates, _⟩
  have oneEquation := (Modules.Constant.outputRule_holds_iff .bit true
    _ oneState _).mp (oneEvaluates.1 Primitives.ConstantRule.apply)
  rcases (children width .ripple).hasCorrespondingState
      (structuralState .ripple) with ⟨rippleState, rippleCorresponds⟩
  rcases Contracts.Cycle.Certification.childImplements (children width) inputs structuralState proposal
      satisfies .ripple rippleState rippleCorresponds with
    ⟨_, rippleEvaluates, _⟩
  have rippleEquation := (Ripple.outputRule_holds_iff width _ rippleState _).mp
    (rippleEvaluates.1 Ripple.Rule.apply)
  have rippleInputsEquation : ProposedValues.childInputs (body width) _ inputs
      proposal.2 .ripple = rippleInputs width inputs (proposal.2 .one) := by
    funext port; cases port <;> rfl
  rw [rippleInputsEquation] at rippleEquation
  have resultEquation := rippleEquation.1
  change (proposal.2 .ripple).outputs .result =
    (addCarry width (inputs .value) ((proposal.2 .one).outputs .output)).1
      at resultEquation
  rw [oneEquation] at resultEquation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .result =
        (proposal.2 .ripple).outputs .result by exact boundary .result]
    exact resultEquation
  · funext label
    exact nomatch label

private noncomputable def proofCertification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := by
    rw [moduleStructure_eq width]
    exact compositeHasStructuralResult width
  structuralResultUnique := by
    rw [moduleStructure_eq width]
    exact (schedules width).hasAtMostOneSolution (coversChildren width)
  implements := by
    rw [moduleStructure_eq width]
    exact compositeImplements width

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (proofCertification width).bundle

end Silean.Modules.Increment

namespace Silean.Modules.Increment.Ripple.Naming

open Silean Silean.Naming

private def ports (width : Nat) : ModulePortsNaming (Ripple.ports width) where
  inputs := ⟨fun | .value => "value" | .carryIn => "carry_in"⟩
  outputs := ⟨fun | .result => "result" | .carryOut => "carry_out"⟩
  inputTypes := fun | .value => .vector .bit | .carryIn => .bit
  outputTypes := fun | .result => .vector .bit | .carryOut => .bit

private def naming : (width : Nat) → ModuleNaming (Ripple.moduleStructure width)
  | 0 => by
      rw [Ripple.moduleStructure.eq_def]
      exact .composite ⟨"increment_ripple", "base", []⟩ (ports 0)
        (fun | Ripple.BaseInstance.empty => "empty")
        (fun
          | Ripple.BaseInstance.empty =>
              Modules.Constant.Naming.naming (.vector 0 .bit) Ripple.emptyValue)
  | width + 1 => by
      rw [Ripple.moduleStructure.eq_def]
      exact .composite
        ⟨"increment_ripple", "recursive", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .split => "split"
          | .lowerBits => "lower_bits"
          | .lowerRipple => "increment_lower"
          | .highAdder => "add_high"
          | .highBit => "high_bit"
          | .concat => "concat")
        (fun
          | .split => Silean.Naming.SignalAdapter.splitter (Ripple.splitter width)
          | .lowerBits =>
              Silean.Naming.SignalAdapter.combiner (Ripple.lowerCombiner width)
          | .lowerRipple => naming width
          | .highAdder => HalfAdder.Naming.naming
          | .highBit => Silean.Naming.SignalAdapter.combiner Ripple.highCombiner
          | .concat => VectorConcat.Naming.naming .bit width 1)

end Silean.Modules.Increment.Ripple.Naming

namespace Silean.Modules.Increment.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.Increment.ports width) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => .vector .bit
  outputTypes := fun | .result => .vector .bit

def naming (width : Nat) : ModuleNaming (Modules.Increment.moduleStructure width) := by
  unfold Modules.Increment.moduleStructure
  exact .composite ⟨"increment", "structural", [.natural width]⟩ (ports width)
    (fun | Modules.Increment.Instance.one => "one"
         | Modules.Increment.Instance.ripple => "ripple")
    (fun
      | Modules.Increment.Instance.one => Modules.Constant.Naming.naming .bit true
      | Modules.Increment.Instance.ripple => Ripple.Naming.naming width)

def namedModule (width : Nat) : NamedModule where
  ports := Modules.Increment.ports width
  moduleStructure := Modules.Increment.moduleStructure width
  naming := naming width

end Silean.Modules.Increment.Naming
