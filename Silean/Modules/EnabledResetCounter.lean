import Silean.Contracts.Cycle.CycleLayerConstruction
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

@[reducible] private def childContracts (width : Nat)
    (resetValue : Value width) : Contracts.Cycle.ChildCycleContracts (body width)
  | .increment => Increment.cycleContract width
  | .storage => EnabledResetRegister.cycleContract (valueType width) resetValue

@[reducible] private def structuralChildren (width : Nat)
    (resetValue : Value width) :
    (name : (instancePorts width).Name) → ModuleStructure ((instancePorts width).ports name)
  | .increment => Increment.moduleStructure width
  | .storage => EnabledResetRegister.moduleStructure (valueType width) resetValue

def moduleStructure (width : Nat) (resetValue : Value width) :
    ModuleStructure (ports width) :=
  .composite (body width) (structuralChildren width resetValue)

@[reducible] private noncomputable def certifiedChildren (width : Nat)
    (resetValue : Value width) :
    (name : (instancePorts width).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (childContracts width resetValue name)
  | .increment =>
      ⟨(Increment.certified width).moduleStructure,
        (Increment.certified width).certification⟩
  | .storage =>
      ⟨(EnabledResetRegister.certified (valueType width) resetValue).moduleStructure,
        (EnabledResetRegister.certified (valueType width) resetValue).certification⟩

private abbrev incrementRule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body width) (childContracts width resetValue) :=
  ⟨.increment, Increment.Rule.apply⟩

private abbrev storageRule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body width) (childContracts width resetValue) :=
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
    Contracts.Cycle.Certification.Layer.OutputSchedule
      (body width) (childContracts width resetValue)
      (cycleContract width resetValue) .observe :=
  .call (storageRule width resetValue)
    (by intro input member; simp [storageRule_reads] at member)
    (by simp)
  (.done (by
    intro output _
    cases output
    exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩))

private def stateSchedule (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (body width) (childContracts width resetValue) :=
  .call (storageRule width resetValue)
    (by intro input member; simp [storageRule_reads] at member)
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
    Contracts.Cycle.Certification.Layer.RuleSchedules
      (body width) (childContracts width resetValue)
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
      left
      change incrementRule width resetValue ∈
        (stateSchedule width resetValue).finalAvailability
      simp [stateSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]
  | storage =>
      change EnabledResetRegister.Rule at rule
      cases rule
      right
      refine ⟨.observe, ?_⟩
      change storageRule width resetValue ∈
        (outputSchedule width resetValue).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

section LayerCertification

variable (width : Nat) (resetValue : Value width)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body width) (childContracts width resetValue))

private def stateCorresponds
    (contractState : (cycleContract width resetValue).state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width) layerChildren)
      (cycleContract width resetValue)
      (stateCorresponds width resetValue layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren
      inputs structuralState proposal satisfies
      .storage contractState corresponds
  have incrementStateSubsingleton :
      Subsingleton (childContracts width resetValue .increment).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have incrementMatches :=
    letI := incrementStateSubsingleton
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren
      inputs structuralState proposal satisfies
      .increment SignalMap.emptyValues
  rcases proposal with ⟨outputs, proposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases incrementMatches with ⟨incrementEvaluates, _⟩
  let storageNextState :=
    (childContracts width resetValue .storage).stateRule.apply
      (ProposedValues.childInputs (body width)
        (fun child => (layerChildren child).moduleStructure)
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

end LayerCertification

/-- The counter wiring implements its contract for any incrementer and
enabled-reset-register implementations satisfying their public contracts. -/
noncomputable opaque certifiedLayer (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body width)
      (childContracts width resetValue) (cycleContract width resetValue) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules width resetValue) (coversChildren width resetValue)
    (stateCorresponds width resetValue)
    (fun children structuralState =>
      (children .storage).certification.hasCorrespondingState
        (structuralState .storage))
    (implements width resetValue)

private noncomputable opaque certification (width : Nat)
    (resetValue : Value width) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width resetValue)
      (cycleContract width resetValue) :=
  (certifiedLayer width resetValue).certifyComposite
    (structuralChildren width resetValue) (certifiedChildren width resetValue)
    (by
      intro child
      cases child with
      | increment => rfl
      | storage =>
          exact EnabledResetRegister.certified_moduleStructure
            (valueType width) resetValue)

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
