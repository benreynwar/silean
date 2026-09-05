import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Foundation.BitVector
import Silean.Modules.Constant
import Silean.Modules.Mask
import Silean.Modules.VectorConcat.VectorConcatCertified
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Not

namespace Silean.Modules.BinaryToOneHot

open Silean
open Contracts.Cycle.Certification.Layer

/-! A combinational binary-to-one-hot decoder. For a `width`-bit input, exactly
one of the `2 ^ width` output bits is asserted. -/

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
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun | .result => oneHot width (inputs .value)

@[reducible] def cycleContract (width : Nat) : Contracts.Cycle.ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule width
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = oneHot width (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

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

/-! ## Hardware structure

Width zero is the one-element constant vector `[true]`. A successor width
splits off the highest-index bit, rebuilds the lower-bit vector, recursively
decodes it, masks two copies with the high bit and its inverse, then joins
the halves. -/

private def baseValue : (SignalType.vector 1 .bit).Denote := fun _ => true

private inductive BaseInstance
  /-- Supplies the sole asserted output for a zero-width input. -/
  | constant
deriving Enumeration

@[reducible] private def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .constant => Modules.Constant.ports (.vector 1 .bit)

@[reducible] private def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

private def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput | .result => baseContext.instanceOutput .constant .output
  instanceInput | .constant, impossible => nomatch impossible

@[reducible] private def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

private def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .constant => Modules.Constant.moduleStructure (.vector 1 .bit) baseValue

private def splitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
private def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
private def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

inductive SuccInstance
  /-- Exposes the individual input bits. -/
  | split
  /-- Rebuilds the lower input bits for the recursive decoder. -/
  | lowerBits
  /-- Recursively decodes the lower bits. -/
  | decode
  /-- Inverts the high bit for the lower output half. -/
  | invert
  /-- Enables the lower half when the high bit is zero. -/
  | lowerMask
  /-- Enables the upper half when the high bit is one. -/
  | upperMask
  /-- Joins the two halves into the one-hot result. -/
  | concat
deriving Enumeration

@[reducible] def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .decode => ports width
    | .invert => Primitives.not.ports
    | .lowerMask | .upperMask => Modules.Mask.ports (.vector (size width) .bit)
    | .concat => Modules.VectorConcat.ports .bit (size width) (size width)

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    -- The concatenated masked halves form the result.
    | .result => (succContext width).instanceOutput .concat .result
  instanceInput
    -- Split the input and rebuild its lower bits.
    | .split, .value => (succContext width).moduleInput .value
    | .lowerBits, index =>
        (succContext width).instanceOutput .split index.castSucc
    | .decode, .value =>
        (succContext width).instanceOutput .lowerBits .value
    -- Use the high bit to select one copy of the recursive result.
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
    -- Join the selected lower and upper halves.
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
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private def baseChildContracts : Contracts.Cycle.ChildCycleContracts baseBody
  | .constant => Modules.Constant.cycleContract (.vector 1 .bit) baseValue

private abbrev baseOccurrence :
    Contracts.Cycle.Certification.Layer.RuleOccurrence baseBody baseChildContracts :=
  ⟨.constant, Primitives.ConstantRule.apply⟩

private def baseScheduleOrders : ScheduleDerivation.RuleScheduleOrders
    baseBody baseChildContracts (cycleContract 0) where
  output | .apply => [baseOccurrence]
  state := []

private def baseDerivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    baseBody baseChildContracts (cycleContract 0) := by
  derive_rule_schedules baseScheduleOrders

private abbrev baseSchedules := baseDerivedRuleSchedules.schedules

private theorem baseCoversChildren : baseSchedules.CoversChildren :=
  baseDerivedRuleSchedules.coversChildren

private theorem baseImplements
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      baseBody baseChildContracts) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure baseBody layerChildren)
      (cycleContract 0) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childStateSubsingleton :
      Subsingleton (baseChildContracts .constant).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have childEvaluates :=
    letI := childStateSubsingleton
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .constant SignalMap.emptyValues).1
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
      (.vector 1 .bit) baseValue _ SignalMap.emptyValues _).mp
      (childEvaluates.1 Primitives.ConstantRule.apply)
    change (proposal.snd .constant).outputs .output index = _
    exact (congrFun constantRule index).trans (by
      simp [baseValue, oneHot, BitVector.toNat])
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private noncomputable opaque baseCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer baseBody baseChildContracts
      (cycleContract 0) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    baseSchedules baseCoversChildren (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) baseImplements

private noncomputable def baseCertifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures baseBody baseChildContracts
  | .constant =>
      (Modules.Constant.certified (.vector 1 .bit) baseValue).certifiedStructure

private noncomputable def baseImplementation : Implementation 0 :=
  (baseCertifiedLayer.certify baseCertifiedChildren).transportStructure (by rfl)

@[reducible] private def succChildContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody width)
  | .split => (splitter width).cycleContract
  | .lowerBits => (lowerCombiner width).cycleContract
  | .decode => cycleContract width
  | .invert => Primitives.notCycleContract
  | .lowerMask | .upperMask => Modules.Mask.cycleContract (.vector (size width) .bit)
  | .concat => Modules.VectorConcat.cycleContract .bit (size width) (size width)

private abbrev splitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerBits, Composition.SignalComponentRule.apply⟩
private abbrev decodeOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.decode, Rule.apply⟩
private abbrev invertOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.invert, Primitives.NotRule.apply⟩
private abbrev lowerOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerMask, Modules.Mask.Rule.apply⟩
private abbrev upperOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.upperMask, Modules.Mask.Rule.apply⟩
private abbrev concatOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.concat, Modules.VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output := fun
    | .apply => [splitOccurrence width, lowerBitsOccurrence width,
        decodeOccurrence width, invertOccurrence width, lowerOccurrence width,
        upperOccurrence width, concatOccurrence width]
  state := []

private def succDerivedRuleSchedules (width : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) := by
  derive_rule_schedules (succScheduleOrders width)

private abbrev succSchedules (width : Nat) :=
  (succDerivedRuleSchedules width).schedules

private theorem succCoversChildren (width : Nat) :
    (succSchedules width).CoversChildren :=
  (succDerivedRuleSchedules width).coversChildren

private def splitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private def lowerBitsInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split index.castSucc

private def decodeInputs (width : Nat)
    (lowerBits : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .value => lowerBits .value

private def invertInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    Primitives.not.ports.inputs.Values
  | .input => split (highIndex width)

private def lowerInputs (width : Nat)
    (decoded : (ports width).outputs.Values)
    (inverted : Primitives.not.ports.outputs.Values) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded .result
  | .mask => inverted .output

private def upperInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values)
    (decoded : (ports width).outputs.Values) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded .result
  | .mask => split (highIndex width)

private def concatInputs (width : Nat)
    (lower upper : (Modules.Mask.ports (.vector (size width) .bit)).outputs.Values) :
    (Modules.VectorConcat.ports .bit (size width) (size width)).inputs.Values
  | .left => lower .result
  | .right => upper .result

private theorem succImplements (width : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure (succBody width) layerChildren)
      (cycleContract (width + 1))
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child, (succChildContracts width child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (succChildContracts width child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies childStates childStateSubsingleton
  have splitOutputs : (proposal.snd .split).outputs =
      (splitter width).outputValues (splitInputs width inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter width) _ _ _).mp
      ((childMatches .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (succBody width)
        (fun child => (layerChildren child).moduleStructure)
        inputs proposal.snd .split = splitInputs width inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerOutputs : (proposal.snd .lowerBits).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.snd .lowerBits) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerBits).1.1 Composition.SignalComponentRule.apply)

  have decodedEquation := (outputRule_holds_iff width _ SignalMap.emptyValues _).mp
    ((childMatches .decode).1.1 Rule.apply)

  have invertEquation := (Primitives.notOutputRule_holds_iff
    _ SignalMap.emptyValues _).mp
    ((childMatches .invert).1.1 Primitives.NotRule.apply)

  have lowerEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ SignalMap.emptyValues _).mp
      ((childMatches .lowerMask).1.1 Modules.Mask.Rule.apply)

  have upperEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ SignalMap.emptyValues _).mp
      ((childMatches .upperMask).1.1 Modules.Mask.Rule.apply)

  have concatEquation := (Modules.VectorConcat.outputRule_holds_iff
    .bit (size width) (size width) _ SignalMap.emptyValues _).mp
      ((childMatches .concat).1.1 Modules.VectorConcat.Rule.apply)

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
          lowerBitsInputs width (proposal.snd .split).outputs := by
      funext index
      rfl
    have decodeInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .decode =
          decodeInputs width (proposal.snd .lowerBits).outputs := by
      funext port; cases port; rfl
    have invertInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .invert =
          invertInputs width (proposal.snd .split).outputs := by
      funext port; cases port; rfl
    have lowerInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .lowerMask =
          lowerInputs width (proposal.snd .decode).outputs
            (proposal.snd .invert).outputs := by
      funext port; cases port <;> rfl
    have upperInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .upperMask =
          upperInputs width (proposal.snd .split).outputs
            (proposal.snd .decode).outputs := by
      funext port; cases port <;> rfl
    have concatInputsEquation : ProposedValues.childInputs (succBody width) _
        inputs proposal.snd .concat =
          concatInputs width (proposal.snd .lowerMask).outputs
            (proposal.snd .upperMask).outputs := by
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

private noncomputable opaque succCertifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (succSchedules width) (succCoversChildren width) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (succImplements width)

private noncomputable def succCertifiedChildren (width : Nat)
    (previous : Implementation width) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)
  | .split => (splitter width).certified.certifiedStructure
  | .lowerBits => (lowerCombiner width).certified.certifiedStructure
  | .decode => previous.certified.certifiedStructure
  | .invert => Primitives.notCertified.certifiedStructure
  | .lowerMask | .upperMask =>
      (Modules.Mask.certified (.vector (size width) .bit)).certifiedStructure
  | .concat =>
      (Modules.VectorConcat.certified .bit (size width) (size width)).certifiedStructure

private noncomputable def succImplementation (width : Nat)
    (previous : Implementation width) : Implementation (width + 1) :=
  ((succCertifiedLayer width).certify (succCertifiedChildren width previous)).transportStructure
    (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

noncomputable def implementation : (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementation width)

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Silean.Modules.BinaryToOneHot

namespace Silean.Modules.BinaryToOneHot.Naming

open Silean Silean.Naming

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
          | .split => Silean.Naming.SignalAdapter.splitter
              (Modules.BinaryToOneHot.splitter width)
          | .lowerBits => Silean.Naming.SignalAdapter.combiner
              (Modules.BinaryToOneHot.lowerCombiner width)
          | .decode => naming width
          | .invert => Silean.Naming.Primitive.not
          | .lowerMask | .upperMask => Modules.Mask.Naming.naming
              (.vector (Modules.BinaryToOneHot.size width) .bit)
          | .concat => Modules.VectorConcat.naming .bit
              (Modules.BinaryToOneHot.size width) (Modules.BinaryToOneHot.size width))

def namedModule (width : Nat) : NamedModule where
  ports := Modules.BinaryToOneHot.ports width
  moduleStructure := Modules.BinaryToOneHot.moduleStructure width
  naming := naming width

end Silean.Modules.BinaryToOneHot.Naming
