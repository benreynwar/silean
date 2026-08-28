import Silean.Contracts.Cycle.CycleSchedule
import Silean.Modules.EnabledResetRegister
import Silean.Modules.Increment

namespace Silean.Modules.EnabledResetCounter

open Silean

/-- A wrapping binary counter which increments when enabled and can
synchronously reset to a fixed bit-vector value. -/
abbrev Value (width : Nat) := Fin width → Bool

@[reducible] def valueType (width : Nat) : SignalType :=
  .vector width .bit

inductive Input
  | enable
  | reset
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .enable | .reset => .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .value => valueType width

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap, outputMap width⟩

def nextValue (width : Nat) (resetValue : Value width)
    (enable reset : Bool) (stored : Value width) : Value width :=
  bif reset then resetValue
  else bif enable then Increment.incrementValue width stored else stored

inductive Rule | observe
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) (Register.stateMap (valueType width))
      { inputTypes := .nil, outputTypes := .cons (valueType width) .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap width).select .value
  target | (), state => (state .stored, ())

def stateRule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.CycleStateRule (ports width) (Register.stateMap (valueType width)) where
  inputTypes := .cons .bit (.cons .bit .nil)
  readsInputs := (inputMap.select .reset).prepend .enable
  target := fun | (enable, (reset, ())), state => fun
    | .stored => nextValue width resetValue enable reset (state .stored)

def cycleContract (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleContract (ports width) where
  state := Register.stateMap (valueType width)
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule width⟩
  stateRule := stateRule width resetValue
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem stateRule_apply_stored (width : Nat)
    (resetValue : Value width) (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values) :
    (stateRule width resetValue).apply inputs state .stored =
      nextValue width resetValue (inputs .enable) (inputs .reset)
        (state .stored) := by
  rfl

theorem next_stored_of_reset (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (reset : inputs .reset = true) :
    (stateRule width resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, nextValue, reset]
  rfl

theorem next_stored_of_enabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    (stateRule width resetValue).apply inputs state .stored =
      Increment.incrementValue width (state .stored) := by
  rw [stateRule_apply_stored, nextValue, notReset, enabled]
  rfl

theorem next_stored_of_disabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (disabled : inputs .enable = false) :
    (stateRule width resetValue).apply inputs state .stored = state .stored := by
  rw [stateRule_apply_stored, nextValue, notReset, disabled]
  rfl

theorem next_toNat_of_enabled (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (state : (Register.stateMap (valueType width)).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    BitVector.toNat width ((stateRule width resetValue).apply inputs state .stored) =
      (BitVector.toNat width (state .stored) + 1) % BitVector.cardinality width := by
  rw [next_stored_of_enabled width resetValue inputs state notReset enabled]
  exact Increment.incrementValue_toNat width (state .stored)

/-! ## Hardware structure -/

private inductive Instance
  /-- Computes the current value plus one, wrapping on overflow. -/
  | increment
  /-- Retains, loads, or resets the counter value. -/
  | storage
deriving Enumeration

@[reducible] private def instancePorts (width : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .increment => Increment.ports width
    | .storage => EnabledResetRegister.ports (valueType width)

@[reducible] private def context (width : Nat) : EndpointContext where
  ports := ports width
  instancePorts := instancePorts width

private def wiring (width : Nat) :
    Wiring (context width).ports (context width).instancePorts :=
  let c := context width
  { moduleOutput := fun
    -- Expose the stored counter value.
    | .value => c.instanceOutput .storage .value
    instanceInput := fun
    -- Continuously compute the candidate incremented value.
    | .increment, .value => c.instanceOutput .storage .value
    -- Load that candidate when enabled; reset is handled by the storage child.
    | .storage, .value => c.instanceOutput .increment .result
    | .storage, .enable => c.moduleInput .enable
    | .storage, .reset => c.moduleInput .reset }

@[reducible] private def body (width : Nat) : ModuleBody :=
  ⟨context width, wiring width⟩

@[reducible] private noncomputable def children (width : Nat)
    (resetValue : Value width) : Contracts.Cycle.Certification.Children (body width)
  | .increment => Increment.certified width
  | .storage => EnabledResetRegister.certified (valueType width) resetValue

@[reducible] private noncomputable def childStructure (width : Nat)
    (resetValue : Value width) := Contracts.Cycle.Certification.childStructure (children width resetValue)

@[reducible] private def structuralChildren (width : Nat)
    (resetValue : Value width) :
    (name : (instancePorts width).Name) → ModuleStructure ((instancePorts width).ports name)
  | .increment => Increment.moduleStructure width
  | .storage => EnabledResetRegister.moduleStructure (valueType width) resetValue

def moduleStructure (width : Nat) (resetValue : Value width) :
    ModuleStructure (ports width) :=
  .composite (body width) (structuralChildren width resetValue)

private theorem moduleStructure_eq (width : Nat) (resetValue : Value width) :
    moduleStructure width resetValue =
      Contracts.Cycle.Certification.moduleStructure (body width) (children width resetValue) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

private abbrev incrementRule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.RuleOccurrence (children width resetValue) :=
  ⟨.increment, Increment.Rule.apply⟩

private abbrev storageRule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.RuleOccurrence (children width resetValue) :=
  ⟨.storage, EnabledResetRegister.Rule.observe⟩

@[simp] private theorem incrementRule_reads (width : Nat)
    (resetValue : Value width) :
    (incrementRule width resetValue).reads = [.value] := rfl

@[simp] private theorem incrementRule_writes (width : Nat)
    (resetValue : Value width) :
    (incrementRule width resetValue).writes = [.result] := rfl

@[simp] private theorem storageRule_reads (width : Nat)
    (resetValue : Value width) :
    (storageRule width resetValue).reads = [] := rfl

@[simp] private theorem storageRule_writes (width : Nat)
    (resetValue : Value width) :
    (storageRule width resetValue).writes = [.value] := rfl

private def outputSchedule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.OutputSchedule (body width) (children width resetValue)
      (cycleContract width resetValue) .observe :=
  .call (storageRule width resetValue)
    (by intro input member; rw [storageRule_reads] at member; cases member)
    (by simp)
  (.done (by
    intro output _
    cases output
    exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩))

private def stateSchedule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.StateSchedule (body width) (children width resetValue) :=
  .call (storageRule width resetValue)
    (by intro input member; rw [storageRule_reads] at member; cases member)
    (by simp)
  (.call (incrementRule width resetValue)
    (by intro input _; cases input
        exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | increment =>
        change input ∈ (Contracts.Cycle.CycleStateRule.empty _).readsInputs.labels at member
        exact nomatch member
    | storage =>
        cases input with
        | value => exact ⟨Increment.Rule.apply, by simp, by simp⟩
        | enable | reset => trivial)))

private def ruleSchedules (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.RuleSchedules (body width) (children width resetValue)
      (cycleContract width resetValue) where
  output | .observe => outputSchedule width resetValue
  state := stateSchedule width resetValue

private theorem coversChildren (width : Nat) (resetValue : Value width) :
    (ruleSchedules width resetValue).CoversChildren := by
  intro child rule
  cases child with
  | increment =>
      change Increment.Rule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
      change incrementRule width resetValue ∈
        (stateSchedule width resetValue).finalAvailability
      simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | storage =>
      change EnabledResetRegister.Rule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
      apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs
        (ruleSchedules width resetValue) .observe
      change storageRule width resetValue ∈
        (outputSchedule width resetValue).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (width : Nat) (resetValue : Value width) :
    (Contracts.Cycle.Certification.moduleStructure (body width)
      (children width resetValue)).HasAtMostOneSolution :=
  (ruleSchedules width resetValue).hasAtMostOneSolution
    (coversChildren width resetValue)

private def incrementInputs (width : Nat) (stored : Value width) :
    (Increment.ports width).inputs.Values
  | .value => stored

private noncomputable def storageInputs (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (increment : ProposedValues (children width resetValue .increment).moduleStructure) :
    (EnabledResetRegister.ports (valueType width)).inputs.Values
  | .value => increment.outputs .result
  | .enable => inputs .enable
  | .reset => inputs .reset

private theorem hasStructuralResult (width : Nat) (resetValue : Value width)
    (inputs : (ports width).inputs.Values)
    (currentState : (Contracts.Cycle.Certification.moduleStructure (body width)
      (children width resetValue)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (body width)
      (children width resetValue)).IsSolution inputs currentState proposal := by
  rcases (children width resetValue .storage).hasCorrespondingState
      (currentState .storage) with ⟨storageState, storageCorresponds⟩
  rcases (children width resetValue .increment).hasStructuralResult
      (incrementInputs width (storageState .stored))
      (currentState .increment) with ⟨increment, incrementSatisfies⟩
  rcases (children width resetValue .storage).hasStructuralResult
      (storageInputs width resetValue inputs increment)
      (currentState .storage) with ⟨storage, storageSatisfies⟩
  have storageOutput : storage.outputs .value = storageState .stored := by
    rcases (children width resetValue .storage).implements
        (storageInputs width resetValue inputs increment) storageState
        (currentState .storage) storage storageCorresponds storageSatisfies with
      ⟨nextState, evaluates, nextCorresponds⟩
    exact (EnabledResetRegister.outputRule_holds_iff (valueType width) _ _ _).mp
      (evaluates.1 EnabledResetRegister.Rule.observe)
  let proposals : (name : Instance) →
      ProposedValues (childStructure width resetValue name)
    | .increment => increment
    | .storage => storage
  let outputs : (ports width).outputs.Values := fun
    | .value => storage.outputs .value
  refine ⟨ProposedValues.composite outputs proposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | increment =>
        change (children width resetValue .increment).moduleStructure.IsSolution
          (ProposedValues.childInputs (body width) (childStructure width resetValue)
            inputs proposals .increment) (currentState .increment) increment
        rw [show ProposedValues.childInputs (body width)
          (childStructure width resetValue) inputs proposals .increment =
            incrementInputs width (storageState .stored) by
          funext port; cases port; exact storageOutput]
        exact incrementSatisfies
    | storage =>
        change (children width resetValue .storage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body width) (childStructure width resetValue)
            inputs proposals .storage) (currentState .storage) storage
        rw [show ProposedValues.childInputs (body width)
          (childStructure width resetValue) inputs proposals .storage =
            storageInputs width resetValue inputs increment by
          funext port; cases port <;> rfl]
        exact storageSatisfies

private def stateCorresponds (width : Nat) (resetValue : Value width)
    (contractState : (cycleContract width resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body width)
      (children width resetValue)).State) : Prop :=
  (children width resetValue .storage).stateCorresponds contractState
    (structuralState .storage)

private theorem implements (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body width) (children width resetValue))
      (cycleContract width resetValue) (stateCorresponds width resetValue) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children width resetValue) inputs structuralState proposal satisfies
      .storage contractState corresponds
  rcases (children width resetValue .increment).hasCorrespondingState
      (structuralState .increment) with ⟨incrementState, incrementCorresponds⟩
  have incrementState_eq : incrementState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst incrementState
  have incrementMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children width resetValue) inputs structuralState proposal satisfies
      .increment SignalMap.emptyValues incrementCorresponds
  rcases proposal with ⟨outputs, proposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases incrementMatches with ⟨incrementEvaluates, _⟩
  let storageNextState :=
    (children width resetValue .storage).cycleContract.stateRule.apply
      (ProposedValues.childInputs (body width) (childStructure width resetValue)
        inputs proposals .storage) contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule width).Holds inputs contractState outputs
    rw [outputRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((EnabledResetRegister.outputRule_holds_iff (valueType width) _ _ _).mp
        (storageEvaluates.1 EnabledResetRegister.Rule.observe))
  · have storageNextValue : storageNextState .stored =
        bif inputs .reset then resetValue
        else bif inputs .enable then (proposals .increment).outputs .result
          else contractState .stored := by
      exact EnabledResetRegister.stateRule_apply_stored
        (valueType width) resetValue _ _
    have incremented := Increment.result_of_evaluatesTo width _ _ _ _
      incrementEvaluates
    change (proposals .increment).outputs .result =
      Increment.incrementValue width ((proposals .storage).outputs .value) at incremented
    have storageCurrent :=
      (EnabledResetRegister.outputRule_holds_iff (valueType width) _ _ _).mp
        (storageEvaluates.1 EnabledResetRegister.Rule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif inputs .reset then resetValue
      else bif inputs .enable then (proposals .increment).outputs .result
        else contractState .stored) =
      nextValue width resetValue (inputs .enable) (inputs .reset)
        (contractState .stored)
    rw [incremented, storageCurrent]
    rfl

private noncomputable def proofCertification (width : Nat)
    (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (body width) (children width resetValue))
      (cycleContract width resetValue) where
  stateCorresponds := stateCorresponds width resetValue
  hasCorrespondingState := fun structuralState =>
    (children width resetValue .storage).hasCorrespondingState
      (structuralState .storage)
  hasStructuralResult := hasStructuralResult width resetValue
  structuralResultUnique := hasAtMostOneSolution width resetValue
  implements := implements width resetValue

private noncomputable opaque certification (width : Nat)
    (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width resetValue)
      (cycleContract width resetValue) :=
  (proofCertification width resetValue).transportStructure
    (moduleStructure_eq width resetValue).symm

noncomputable def certified (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width resetValue).bundle

@[simp] theorem certified_moduleStructure (width : Nat) (resetValue : Value width) :
    (certified width resetValue).moduleStructure = moduleStructure width resetValue := rfl

@[simp] theorem certified_cycleContract (width : Nat) (resetValue : Value width) :
    (certified width resetValue).cycleContract = cycleContract width resetValue := rfl

end Silean.Modules.EnabledResetCounter

namespace Silean.Modules.EnabledResetCounter.Naming

open Silean Silean.Naming

def ports (width : Nat) :
    ModulePortsNaming (Modules.EnabledResetCounter.ports width) where
  inputs := ⟨fun | .enable => "enable" | .reset => "reset"⟩
  outputs := ⟨fun | .value => "value"⟩
  outputTypes := fun | .value => .vector .bit

def naming (width : Nat) (resetValue : Modules.EnabledResetCounter.Value width) :
    ModuleNaming (Modules.EnabledResetCounter.moduleStructure width resetValue) := by
  unfold Modules.EnabledResetCounter.moduleStructure
  exact .composite
    ⟨"enabled_reset_counter", "structural",
      .natural width :: Modules.Constant.Naming.parameters
        (.vector width .bit) resetValue⟩
    (ports width)
    (fun | .increment => "increment" | .storage => "storage")
    (fun
      | .increment => Modules.Increment.Naming.naming width
      | .storage => Modules.EnabledResetRegister.Naming.naming
          (.vector width .bit) resetValue)

end Silean.Modules.EnabledResetCounter.Naming
