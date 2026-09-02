import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Constant
import Silean.Modules.Mux
import Silean.Modules.Register

namespace Silean.Modules.ResetRegister

open Silean
open Contracts.Cycle.Certification.Layer

/-! ## Hardware structure -/

/-- A register which stores `value`, except that reset selects a fixed value. -/
inductive Instance
  /-- Produces the value loaded during reset. -/
  | resetValue
  /-- Chooses between the ordinary input and reset value. -/
  | selection
  /-- Holds the selected value across cycles. -/
  | storage
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType)
    (_resetValue : signalType.Denote) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .resetValue => Constant.ports signalType
    | .selection => Mux.ports signalType
    | .storage => Register.ports signalType

inductive Input
  | value
  | reset
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => signalType
    | .reset => .bit

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .value => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType)
    (resetValue : signalType.Denote) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType resetValue

def wiring (signalType : SignalType) (resetValue : signalType.Denote) :
    Wiring (context signalType resetValue).ports
      (context signalType resetValue).instancePorts :=
  let c := context signalType resetValue
  { moduleOutput := fun
    -- The stored value is exposed directly.
    | .value => c.instanceOutput .storage .output
    instanceInput := fun
    | .resetValue, impossible => nomatch impossible
    -- Reset selects the constant; otherwise select the ordinary input.
    | .selection, .select =>
        c.moduleInput .reset
    | .selection, .whenFalse =>
        c.moduleInput .value
    | .selection, .whenTrue =>
        c.instanceOutput .resetValue .output
    -- Store the selected value on the next clock edge.
    | .storage, .input =>
        c.instanceOutput .selection .result }

@[reducible] def body (signalType : SignalType)
    (resetValue : signalType.Denote) : ModuleBody :=
  ⟨context signalType resetValue, wiring signalType resetValue⟩

@[reducible] private def childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ChildCycleContracts (body signalType resetValue)
  | .resetValue => Constant.cycleContract signalType resetValue
  | .selection => Mux.cycleContract signalType
  | .storage => Register.cycleContract signalType

@[reducible] private def structuralChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instancePorts signalType resetValue).Name) →
      ModuleStructure ((instancePorts signalType resetValue).ports name)
  | .resetValue => Constant.moduleStructure signalType resetValue
  | .selection => Mux.moduleStructure signalType
  | .storage => Register.moduleStructure signalType

def moduleStructure (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType resetValue) (structuralChildren signalType resetValue)

@[reducible] private noncomputable def certifiedChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instancePorts signalType resetValue).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (childContracts signalType resetValue name)
  | .resetValue =>
      ⟨(Constant.certified signalType resetValue).moduleStructure,
        (Constant.certified signalType resetValue).certification⟩
  | .selection => Mux.certifiedStructure signalType
  | .storage =>
      ⟨(Register.certified signalType).moduleStructure,
        (Register.certified signalType).certification⟩

/-! ## Exact cycle behavior and certification -/

inductive Rule | observe
deriving Enumeration

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .value
  target | (), state => (state .stored, ())

def stateRule (signalType : SignalType) (resetValue : signalType.Denote) :
    Contracts.Cycle.CycleStateRule (ports signalType) (Register.stateMap signalType) where
  inputTypes := .cons .bit (.cons signalType .nil)
  readsInputs := ((inputMap signalType).select .value).prepend .reset
  target := fun | (reset, (value, ())), _ => fun
    | .stored => bif reset then resetValue else value

def cycleContract (signalType : SignalType) (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := Register.stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType resetValue
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem stateRule_apply_stored (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values) :
    (stateRule signalType resetValue).apply inputs state .stored =
      bif inputs .reset then resetValue else inputs .value := by
  rfl

theorem next_stored_of_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (reset : inputs .reset = true) :
    (stateRule signalType resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, reset]
  rfl

theorem next_stored_of_not_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) :
    (stateRule signalType resetValue).apply inputs state .stored = inputs .value := by
  rw [stateRule_apply_stored, notReset]
  rfl

private abbrev constantRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType resetValue) (childContracts signalType resetValue) :=
  ⟨.resetValue, Primitives.ConstantRule.apply⟩

private abbrev selectionRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType resetValue) (childContracts signalType resetValue) :=
  ⟨.selection, Mux.Rule.select⟩

private abbrev storageRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType resetValue) (childContracts signalType resetValue) :=
  ⟨.storage, Primitives.RegisterRule.observe⟩

private def scheduleOrders (signalType : SignalType)
    (resetValue : signalType.Denote) : ScheduleDerivation.RuleScheduleOrders
      (body signalType resetValue) (childContracts signalType resetValue)
      (cycleContract signalType resetValue) where
  output | .observe => [storageRule signalType resetValue]
  state := [constantRule signalType resetValue, selectionRule signalType resetValue]

private def derivedRuleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) : ScheduleDerivation.DerivedRuleSchedules
      (body signalType resetValue) (childContracts signalType resetValue)
      (cycleContract signalType resetValue) := by
  derive_rule_schedules (scheduleOrders signalType resetValue)

private abbrev ruleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) :=
  (derivedRuleSchedules signalType resetValue).schedules

private theorem coversChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (ruleSchedules signalType resetValue).CoversChildren :=
  (derivedRuleSchedules signalType resetValue).coversChildren

section LayerCertification

variable (signalType : SignalType) (resetValue : signalType.Denote)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body signalType resetValue) (childContracts signalType resetValue))

private def stateCorresponds
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType resetValue) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType resetValue) layerChildren)
      (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have statelessChildState (child : Instance)
      (h : child = .resetValue ∨ child = .selection) :
      Subsingleton (childContracts signalType resetValue child).state.Values := by
    rcases h with rfl | rfl <;>
      change Subsingleton emptySignalMap.Values <;> infer_instance
  have constantMatches :=
    letI := statelessChildState .resetValue (Or.inl rfl)
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .resetValue SignalMap.emptyValues
  have selectionMatches :=
    letI := statelessChildState .selection (Or.inr rfl)
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      .selection SignalMap.emptyValues
  have storageMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren
      inputs structuralState proposal satisfies
      .storage contractState corresponds
  rcases constantMatches with ⟨constantEvaluates, _⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases proposal with ⟨outputs, childProposals⟩
  let nextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
    (ProposedValues.childInputs (body signalType resetValue)
      (fun child => (layerChildren child).moduleStructure)
      inputs childProposals .storage) contractState
  refine ⟨nextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule signalType).Holds inputs contractState _
    rw [outputRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((Register.outputRule_holds_iff signalType _ _ _).mp
        (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    have constantValue := (Constant.outputRule_holds_iff signalType resetValue _ _ _).mp
      (constantEvaluates.1 Primitives.ConstantRule.apply)
    have storageNextValue : nextState .stored =
        (ProposedValues.childInputs (body signalType resetValue)
          (fun child => (layerChildren child).moduleStructure)
          inputs childProposals .storage) .input := by
      rfl
    change (childProposals .selection).outputs .result =
      bif inputs .reset then
        (childProposals .resetValue).outputs .output else inputs .value at selected
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (childProposals .selection).outputs .result =
      bif inputs .reset then resetValue else inputs .value
    rw [selected, constantValue]

end LayerCertification

/-- The reset-register wiring implements its contract for any constant, mux,
and register implementations satisfying their public contracts. -/
noncomputable opaque certifiedLayer (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body signalType resetValue)
      (childContracts signalType resetValue)
      (cycleContract signalType resetValue) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType resetValue) (coversChildren signalType resetValue)
    (stateCorresponds signalType resetValue)
    (fun children structuralState =>
      (children .storage).certification.hasCorrespondingState
        (structuralState .storage))
    (implements signalType resetValue)

private noncomputable opaque certification (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue) :=
  (certifiedLayer signalType resetValue).certifyComposite
    (structuralChildren signalType resetValue)
    (certifiedChildren signalType resetValue)
    (by
      intro child
      cases child with
      | resetValue => exact Constant.certified_moduleStructure signalType resetValue
      | selection => exact Mux.certifiedStructure_moduleStructure signalType
      | storage => exact Register.certified_moduleStructure signalType)

noncomputable def certified (signalType : SignalType)
    (resetValue : signalType.Denote) : Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType resetValue).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (certified signalType resetValue).moduleStructure =
      moduleStructure signalType resetValue := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (certified signalType resetValue).cycleContract =
      cycleContract signalType resetValue := rfl

end Silean.Modules.ResetRegister

namespace Silean.Modules.ResetRegister.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.ResetRegister.ports signalType) where
  inputs := ⟨fun | .value => "value" | .reset => "reset"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .reset => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.ResetRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (resetValue : signalType.Denote)
    (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.ResetRegister.moduleStructure signalType resetValue) := by
  unfold Modules.ResetRegister.moduleStructure
  exact .composite
    ⟨"reset_register", "structural",
      .shape signalType :: Modules.Constant.Naming.parameters signalType resetValue⟩
    (portsWithNaming signalType typeNaming)
    (fun | .resetValue => "reset_value" | .selection => "selection" | .storage => "storage")
    (fun
      | .resetValue => Modules.Constant.Naming.namingWith signalType resetValue typeNaming
      | .selection => Modules.Mux.Naming.namingWith signalType typeNaming
      | .storage => Modules.Register.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleNaming (Modules.ResetRegister.moduleStructure signalType resetValue) :=
  namingWith signalType resetValue (.positional signalType)

end Silean.Modules.ResetRegister.Naming
