import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Foundation.BitVector
import Silean.Modules.Add
import Silean.Modules.BitwiseXor
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.AddSub

open Silean

/-! Fixed-width addition and subtraction. The behavioral contract below uses
direct carry/borrow recursion. The hardware separately implements subtraction
as `left + ~right + 1`. -/

inductive Input | left | right | subtract
deriving Enumeration

inductive Output
  | result
  /-- Addition carry, or subtraction no-borrow when `subtract` is asserted. -/
  | carryOut
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .left | .right => .vector width .bit
    | .subtract => .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector width .bit
    | .carryOut => .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

private def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

private def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

private def borrowBit (left right borrow : Bool) : Bool :=
  (!left && (right || borrow)) || (right && borrow)

/-! In subtraction mode the internal chain is borrow and the returned flag is
its complement, so `carryOut = true` means that no borrow occurred. -/
private def operate : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → Bool → (Fin width → Bool) × Bool
  | 0, _, _, subtract, chain =>
      (fun index => Fin.elim0 index, if subtract then !chain else chain)
  | width + 1, left, right, subtract, chain =>
      let lower := operate width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      let incoming := if subtract then !lower.2 else lower.2
      let high := sumBit (left (Fin.last width)) (right (Fin.last width)) incoming
      let outgoing := if subtract then
        borrowBit (left (Fin.last width)) (right (Fin.last width)) incoming
      else carryBit (left (Fin.last width)) (right (Fin.last width)) incoming
      (Fin.lastCases high lower.1, if subtract then !outgoing else outgoing)

/-- Natural add/subtract behavior, initialized with neither carry nor borrow. -/
def addSubBits (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :
    (Fin width → Bool) × Bool :=
  operate width left right subtract false

private theorem addBits_transformed : ∀ (width : Nat)
    (left right : Fin width → Bool) (subtract chain : Bool),
    Add.addBits width left
        (fun index => Primitives.xorValue (right index) subtract)
        (if subtract then !chain else chain) =
      operate width left right subtract chain
  | 0, _, _, subtract, chain => by simp [Add.addBits, operate]
  | width + 1, left, right, subtract, chain => by
      have lower := addBits_transformed width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      simp only [Add.addBits, operate]
      rw [lower]
      cases lowerOp : operate width (fun index => left index.castSucc)
          (fun index => right index.castSucc) subtract chain with
      | mk lowerBits lowerFlag =>
          cases subtract <;> cases lowerFlag <;>
            cases leftHigh : left (Fin.last width) <;>
            cases rightHigh : right (Fin.last width) <;>
            simp [Add.sumBit, Add.carryBit, sumBit, carryBit, borrowBit,
              Primitives.xorValue]

private theorem addBits_transformed_initial (width : Nat)
    (left right : Fin width → Bool) (subtract : Bool) :
    Add.addBits width left
        (fun index => Primitives.xorValue (right index) subtract) subtract =
      addSubBits width left right subtract := by
  simpa [addSubBits] using addBits_transformed width left right subtract false

private theorem complemented_toNat : ∀ (width : Nat) (value : Fin width → Bool),
    BitVector.toNat width (fun index => Primitives.xorValue (value index) true) +
        BitVector.toNat width value + 1 = BitVector.cardinality width
  | 0, _ => by simp [BitVector.toNat, BitVector.cardinality]
  | width + 1, value => by
      have lower := complemented_toNat width (fun index => value index.castSucc)
      cases high : value (Fin.last width) <;>
        simp [BitVector.toNat, BitVector.cardinality, high,
          Primitives.xorValue] at lower ⊢ <;>
        omega

/-- The result is ordinary addition or modular subtraction, independent of
the two's-complement implementation used by the structure. -/
theorem addSubBits_result_toNat (width : Nat) (left right : Fin width → Bool)
    (subtract : Bool) :
    BitVector.toNat width (addSubBits width left right subtract).1 =
      if subtract then
        (BitVector.toNat width left + BitVector.cardinality width -
          BitVector.toNat width right) % BitVector.cardinality width
      else
        (BitVector.toNat width left + BitVector.toNat width right) %
          BitVector.cardinality width := by
  have equation := Add.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) subtract) subtract
  rw [addBits_transformed_initial] at equation
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right subtract).1
  have resultBoundPow : BitVector.toNat width (addSubBits width left right subtract).1 <
      2 ^ width := by simpa using resultBound
  cases subtract with
  | false =>
      simp [Primitives.xorValue] at equation ⊢
      rw [← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]
  | true =>
      have complement := complemented_toNat width right
      have rightBound := BitVector.toNat_lt_cardinality width right
      simp at equation ⊢
      rw [BitVector.cardinality_eq_pow] at complement rightBound
      have transformedSum :
          BitVector.toNat width left +
              BitVector.toNat width
                (fun index => Primitives.xorValue (right index) true) + 1 =
            BitVector.toNat width left + 2 ^ width -
              BitVector.toNat width right := by
        omega
      rw [← transformedSum, ← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]

/-- In subtraction mode carry-out is the conventional no-borrow flag. -/
theorem addSubBits_carry_subtract (width : Nat) (left right : Fin width → Bool) :
    (addSubBits width left right true).2 =
      decide (BitVector.toNat width right ≤ BitVector.toNat width left) := by
  have equation := Add.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) true) true
  rw [addBits_transformed_initial] at equation
  have complement := complemented_toNat width right
  have leftBound := BitVector.toNat_lt_cardinality width left
  have rightBound := BitVector.toNat_lt_cardinality width right
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right true).1
  rw [BitVector.cardinality_eq_pow] at complement leftBound rightBound resultBound
  cases carry : (addSubBits width left right true).2 <;>
    by_cases noBorrow : BitVector.toNat width right ≤ BitVector.toNat width left <;>
    simp [carry, noBorrow] at equation ⊢ <;>
    omega

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap
      { inputTypes := .cons (.vector width .bit)
          (.cons (.vector width .bit) (.cons .bit .nil))
        outputTypes := .cons (.vector width .bit) (.cons .bit .nil) } where
  readsInputs := (inputMap width).select .subtract |>.prepend .right |>.prepend .left
  writesOutputs := (outputMap width).select .carryOut |>.prepend .result
  target := fun
    | (left, (right, (subtract, ()))), _ =>
        ((addSubBits width left right subtract).1,
          ((addSubBits width left right subtract).2, ()))

@[reducible] def cycleContract (width : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports width) where
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
      outputs .result =
        (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1 ∧
      outputs .carryOut =
        (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2 := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

/-! ## Hardware structure -/

private def subtractVector (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

private inductive Instance
  /-- Broadcasts `subtract` to every bit position. -/
  | broadcastSubtract
  /-- Complements the right operand exactly in subtraction mode. -/
  | transformRight
  /-- Performs the resulting addition. -/
  | add
deriving Enumeration

@[reducible] private def instancePorts (width : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .broadcastSubtract => (subtractVector width).ports
    | .transformRight => BitwiseXor.ports (.vector width .bit)
    | .add => Add.ports width

@[reducible] private def context (width : Nat) : EndpointContext where
  ports := ports width
  instancePorts := instancePorts width

private def wiring (width : Nat) :
    Wiring (context width).ports (context width).instancePorts where
  moduleOutput
    | .result => (context width).instanceOutput .add .result
    | .carryOut => (context width).instanceOutput .add .carryOut
  instanceInput
    | .broadcastSubtract, _ => (context width).moduleInput .subtract
    | .transformRight, .left => (context width).moduleInput .right
    | .transformRight, .right =>
        (context width).instanceOutput .broadcastSubtract .value
    | .add, .left => (context width).moduleInput .left
    | .add, .right => (context width).instanceOutput .transformRight .result
    | .add, .carryIn => (context width).moduleInput .subtract

@[reducible] private def body (width : Nat) : ModuleBody :=
  ⟨context width, wiring width⟩

@[reducible] private def childContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (body width)
  | .broadcastSubtract => (subtractVector width).cycleContract
  | .transformRight => BitwiseXor.cycleContract (.vector width .bit)
  | .add => Add.cycleContract width

@[reducible] private def structuralChildren (width : Nat) :
    (child : (instancePorts width).Name) → ModuleStructure ((instancePorts width).ports child)
  | .broadcastSubtract => (subtractVector width).certified.moduleStructure
  | .transformRight => BitwiseXor.moduleStructure (.vector width .bit)
  | .add => Add.moduleStructure width

/-- The closed XOR-plus-adder implementation of addition and subtraction. -/
def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  .composite (body width) (structuralChildren width)

@[reducible] private noncomputable def certifiedChildren (width : Nat) :
    (child : (instancePorts width).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts width child)
  | .broadcastSubtract =>
      ⟨(subtractVector width).certified.moduleStructure,
        (subtractVector width).certified.certification⟩
  | .transformRight =>
      ⟨(BitwiseXor.certified (.vector width .bit)).moduleStructure,
        (BitwiseXor.certified (.vector width .bit)).certification⟩
  | .add =>
      ⟨(Add.certified width).moduleStructure,
        (Add.certified width).certification⟩

/-! ## Cycle certification -/

private abbrev broadcastOccurrence (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body width) (childContracts width) :=
  ⟨.broadcastSubtract, Composition.SignalComponentRule.apply⟩

private abbrev xorOccurrence (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body width) (childContracts width) :=
  ⟨.transformRight, BitwiseXor.Rule.apply⟩

private abbrev addOccurrence (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body width) (childContracts width) :=
  ⟨.add, Add.Rule.apply⟩

private def outputSchedule (width : Nat) :
    Contracts.Cycle.Certification.Layer.OutputSchedule (body width) (childContracts width)
      (cycleContract width) .apply :=
  .call (broadcastOccurrence width)
    (by
      intro _ _
      simp [cycleContract, outputRule, Contracts.Cycle.Certification.Layer.sourceAvailable,
        SignalSelection.labels, SignalSelection.prepend, SignalMap.select,
        body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (xorOccurrence width)
    (by
      intro input _
      cases input with
      | left =>
          simp [cycleContract, outputRule, Contracts.Cycle.Certification.Layer.sourceAvailable,
            SignalSelection.labels, SignalSelection.prepend, SignalMap.select,
            body, wiring, context, EndpointContext.moduleInput]
      | right => exact ⟨Composition.SignalComponentRule.apply, by simp, by
          change Composition.AggregatePort.value ∈ [Composition.AggregatePort.value]
          simp⟩)
    (by simp)
  (.call (addOccurrence width)
    (by
      intro input _
      cases input with
      | left | carryIn =>
          simp [cycleContract, outputRule, Contracts.Cycle.Certification.Layer.sourceAvailable,
            SignalSelection.labels, SignalSelection.prepend, SignalMap.select,
            body, wiring, context, EndpointContext.moduleInput]
      | right => exact ⟨BitwiseXor.Rule.apply, by simp, by
          change BitwiseXor.Output.result ∈ [BitwiseXor.Output.result]
          simp⟩)
    (by simp)
  (.done (by
    intro output _
    cases output with
    | result => exact ⟨Add.Rule.apply, by simp, by
        change Add.Output.result ∈ [Add.Output.result, Add.Output.carryOut]
        simp⟩
    | carryOut => exact ⟨Add.Rule.apply, by simp, by
        change Add.Output.carryOut ∈ [Add.Output.result, Add.Output.carryOut]
        simp⟩))))

private def stateSchedule (width : Nat) :
    Contracts.Cycle.Certification.Layer.StateSchedule (body width) (childContracts width) :=
  .done (by
    intro child input member
    cases child with
    | broadcastSubtract =>
        change input ∈ (subtractVector width).cycleContract.stateRule.readsInputs.labels
          at member
        exact nomatch member
    | transformRight =>
        change input ∈ (BitwiseXor.cycleContract (.vector width .bit)).stateRule.readsInputs.labels
          at member
        exact nomatch member
    | add =>
        change input ∈ (Add.cycleContract width).stateRule.readsInputs.labels at member
        exact nomatch member)

private def schedules (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleSchedules (body width) (childContracts width)
      (cycleContract width) where
  output | .apply => outputSchedule width
  state := stateSchedule width

private theorem coversChildren (width : Nat) : (schedules width).CoversChildren := by
  intro child rule
  right
  refine ⟨.apply, ?_⟩
  cases child with
  | broadcastSubtract =>
      change Composition.SignalComponentRule at rule; cases rule
      change broadcastOccurrence width ∈ (outputSchedule width).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]
  | transformRight =>
      change BitwiseXor.Rule at rule; cases rule
      change xorOccurrence width ∈ (outputSchedule width).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]
  | add =>
      change Add.Rule at rule; cases rule
      change addOccurrence width ∈ (outputSchedule width).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

private def broadcastInputs (width : Nat) (inputs : (ports width).inputs.Values) :
    (subtractVector width).ports.inputs.Values := fun _ => inputs .subtract

private def xorInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (broadcast : (subtractVector width).ports.outputs.Values) :
    (BitwiseXor.ports (.vector width .bit)).inputs.Values
  | .left => inputs .right
  | .right => broadcast .value

private def addInputs (width : Nat) (inputs : (ports width).inputs.Values)
    (xor : (BitwiseXor.ports (.vector width .bit)).outputs.Values) :
    (Add.ports width).inputs.Values
  | .left => inputs .left
  | .right => xor .result
  | .carryIn => inputs .subtract

section LayerCertification

variable (width : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body width) (childContracts width))

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1

  have childStateSubsingleton (child : Instance) :
      Subsingleton (childContracts width child).state.Values := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
      proposal satisfies child (by cases child <;> exact SignalMap.emptyValues)
  have broadcastEvaluates := (childMatch .broadcastSubtract).1
  have broadcastEquation := (Composition.SignalCombiner.outputRule_holds_iff
    (subtractVector width) _ SignalMap.emptyValues _).mp
      (broadcastEvaluates.1 Composition.SignalComponentRule.apply)

  have xorEvaluates := (childMatch .transformRight).1
  have xorEquation := BitwiseXor.result_of_evaluatesTo (.vector width .bit)
    _ SignalMap.emptyValues _ _ xorEvaluates

  have addEvaluates := (childMatch .add).1
  have addResult := Add.result_of_evaluatesTo width
    _ SignalMap.emptyValues _ _ addEvaluates
  have addCarry := Add.carry_of_evaluatesTo width
    _ SignalMap.emptyValues _ _ addEvaluates

  have broadcastInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .broadcastSubtract = broadcastInputs width inputs := by
    funext index; rfl
  have xorInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .transformRight =
        xorInputs width inputs (proposal.2 .broadcastSubtract).outputs := by
    funext port; cases port <;> rfl
  have addInputsEquation : ProposedValues.childInputs (body width) _
      inputs proposal.2 .add =
        addInputs width inputs (proposal.2 .transformRight).outputs := by
    funext port; cases port <;> rfl
  rw [broadcastInputsEquation] at broadcastEquation
  rw [xorInputsEquation] at xorEquation
  rw [addInputsEquation] at addResult addCarry

  have broadcastValue : (proposal.2 .broadcastSubtract).outputs .value =
      fun _ => inputs .subtract := by
    rw [congrFun broadcastEquation .value]
    rfl
  have transformedRight : (proposal.2 .transformRight).outputs .result =
      fun index => Primitives.xorValue (inputs .right index) (inputs .subtract) := by
    change (proposal.2 .transformRight).outputs .result =
      SignalType.bitwiseXor (.vector width .bit) (inputs .right)
        ((proposal.2 .broadcastSubtract).outputs .value) at xorEquation
    rw [broadcastValue] at xorEquation
    exact xorEquation
  change (proposal.2 .add).outputs .result =
    (Add.addBits width (inputs .left) ((proposal.2 .transformRight).outputs .result)
      (inputs .subtract)).1 at addResult
  change (proposal.2 .add).outputs .carryOut =
    (Add.addBits width (inputs .left) ((proposal.2 .transformRight).outputs .result)
      (inputs .subtract)).2 at addCarry
  rw [transformedRight] at addResult addCarry
  rw [addBits_transformed_initial] at addResult addCarry

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · rw [show proposal.outputs .result =
          (proposal.2 .add).outputs .result by exact boundary .result]
      exact addResult
    · rw [show proposal.outputs .carryOut =
          (proposal.2 .add).outputs .carryOut by exact boundary .carryOut]
      exact addCarry
  · funext label
    exact nomatch label

end LayerCertification

/-- The add/subtract wiring implements its arithmetic contract for any
children satisfying the broadcast, XOR, and adder contracts. -/
noncomputable opaque certifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body width)
      (childContracts width) (cycleContract width) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (schedules width) (coversChildren width) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (implements width)

noncomputable opaque certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  (certifiedLayer width).certifyComposite
    (structuralChildren width) (certifiedChildren width)
    (by
      intro child
      cases child with
      | broadcastSubtract => rfl
      | transformRight =>
          exact BitwiseXor.certified_moduleStructure (.vector width .bit)
      | add => rfl)

noncomputable def certified (width : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := (certification width).bundle

@[simp] theorem certified_moduleStructure (width : Nat) :
    (certified width).moduleStructure = moduleStructure width := rfl

@[simp] theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

theorem result_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .result =
      (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).1

theorem carry_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut =
      (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).2

/-- Public modular arithmetic law for either selected operation. -/
theorem result_toNat_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    BitVector.toNat width (outputs .result) =
      bif inputs .subtract then
        (BitVector.toNat width (inputs .left) + BitVector.cardinality width -
          BitVector.toNat width (inputs .right)) % BitVector.cardinality width
      else
        (BitVector.toNat width (inputs .left) + BitVector.toNat width (inputs .right)) %
          BitVector.cardinality width := by
  rw [result_of_evaluatesTo width inputs state outputs nextState evaluates]
  have result := addSubBits_result_toNat width
    (inputs .left) (inputs .right) (inputs .subtract)
  cases subtract : inputs .subtract <;> simp [subtract] at result ⊢ <;> exact result

/-- In subtraction mode, the public carry output is true exactly when no
borrow was required. -/
theorem carry_eq_noBorrow_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (subtracts : inputs .subtract = true)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut =
      decide (BitVector.toNat width (inputs .right) ≤
        BitVector.toNat width (inputs .left)) := by
  rw [carry_of_evaluatesTo width inputs state outputs nextState evaluates, subtracts]
  exact addSubBits_carry_subtract width (inputs .left) (inputs .right)

end Silean.Modules.AddSub

namespace Silean.Modules.AddSub.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.AddSub.ports width) where
  inputs := ⟨fun | .left => "left" | .right => "right" | .subtract => "subtract"⟩
  outputs := ⟨fun | .result => "result" | .carryOut => "carry_out"⟩
  inputTypes := fun
    | .left | .right => .vector .bit
    | .subtract => .bit
  outputTypes := fun
    | .result => .vector .bit
    | .carryOut => .bit

def naming (width : Nat) : ModuleNaming (Modules.AddSub.moduleStructure width) := by
  unfold Modules.AddSub.moduleStructure
  exact .composite ⟨"add_sub", "structural", [.natural width]⟩ (ports width)
    (fun
      | .broadcastSubtract => "broadcast_subtract"
      | .transformRight => "transform_right"
      | .add => "add")
    (fun
      | .broadcastSubtract =>
          Silean.Naming.SignalAdapter.combiner (Modules.AddSub.subtractVector width)
      | .transformRight => BitwiseXor.Naming.naming (.vector width .bit)
      | .add => Add.Naming.naming width)

def namedModule (width : Nat) : NamedModule where
  ports := Modules.AddSub.ports width
  moduleStructure := Modules.AddSub.moduleStructure width
  naming := naming width

end Silean.Modules.AddSub.Naming
