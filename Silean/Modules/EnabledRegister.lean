import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Mux
import Silean.Modules.Register

namespace Silean.Modules.EnabledRegister

open Silean
open Contracts.Cycle.Certification.Layer

/-! ## Hardware structure -/

/-- A register which loads `value` when `enable` is high and otherwise retains
its current value. -/
inductive Instance
  /-- Chooses between the new input and the stored value. -/
  | selection
  /-- Holds the selected value across cycles. -/
  | storage
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .selection => Modules.Mux.ports signalType
    | .storage => Modules.Register.ports signalType

inductive Input
  | value
  | enable
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => signalType
    | .enable => .bit

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .value => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- The stored value is exposed directly.
    | .value => c.instanceOutput .storage .output
    instanceInput := fun
    -- Select the new input when enabled, or feed the stored value back.
    | .selection, .select => c.moduleInput .enable
    | .selection, .whenFalse =>
        c.instanceOutput .storage .output
    | .selection, .whenTrue => c.moduleInput .value
    -- Store the mux result on the next clock edge.
    | .storage, .input => c.instanceOutput .selection .result }

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] def childContracts (signalType : SignalType) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .selection => Modules.Mux.cycleContract signalType
  | .storage => Modules.Register.cycleContract signalType

@[reducible] def structuralChildren (signalType : SignalType) :
    (name : (instancePorts signalType).Name) →
      ModuleStructure ((instancePorts signalType).ports name)
  | .selection => Modules.Mux.moduleStructure signalType
  | .storage => Modules.Register.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

@[reducible] noncomputable def certifiedChildren (signalType : SignalType) :
    (name : (instancePorts signalType).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts signalType name)
  | .selection => Modules.Mux.certifiedStructure signalType
  | .storage =>
      ⟨(Modules.Register.certified signalType).moduleStructure,
        (Modules.Register.certified signalType).certification⟩

end Silean.Modules.EnabledRegister

namespace Silean.Modules.EnabledRegister.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) where
  inputs := ⟨fun | .value => "value" | .enable => "enable"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .enable => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) := by
  unfold Modules.EnabledRegister.moduleStructure
  exact .composite ⟨"enabled_register", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun | .selection => "selection" | .storage => "storage")
    (fun
      | .selection => Modules.Mux.Naming.namingWith signalType typeNaming
      | .storage => Modules.Register.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.EnabledRegister.Naming

namespace Silean.Modules.EnabledRegister
open Silean
open Contracts.Cycle.Certification.Layer
/-! ## Exact cycle behavior and certification -/

inductive Rule | observe
deriving Enumeration
def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (Modules.EnabledRegister.ports signalType).outputs.select .value
  target | (), state => (state .stored, ())
def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType) where
  inputTypes := .cons .bit (.cons signalType .nil)
  readsInputs := ((inputMap signalType).select .value).prepend .enable
  target := fun | (enable, (value, ())), state => fun
    | .stored => bif enable then value else state .stored
def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (Modules.EnabledRegister.ports signalType) where
  state := Modules.Register.stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

abbrev selectionRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.selection, Mux.Rule.select⟩

abbrev storageRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.storage, Primitives.RegisterRule.observe⟩

private def scheduleOrders (signalType : SignalType) :
    ScheduleDerivation.RuleScheduleOrders (body signalType)
      (childContracts signalType) (cycleContract signalType) where
  output | .observe => [storageRule signalType]
  state := [storageRule signalType, selectionRule signalType]

private def derivedRuleSchedules (signalType : SignalType) :
    ScheduleDerivation.DerivedRuleSchedules (body signalType)
      (childContracts signalType) (cycleContract signalType) := by
  derive_rule_schedules (scheduleOrders signalType)

private abbrev ruleSchedules (signalType : SignalType) :=
  (derivedRuleSchedules signalType).schedules

private theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren :=
  (derivedRuleSchedules signalType).coversChildren

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body signalType) (childContracts signalType))

private def stateCorresponds
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .storage contractState corresponds
  rcases (layerChildren .selection).certification.hasCorrespondingState
      (structuralState .selection) with ⟨selectionState, selectionCorresponds⟩
  have selectionState_eq : selectionState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst selectionState
  have selectionMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .selection SignalMap.emptyValues
      selectionCorresponds
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (childContracts signalType .storage).stateRule.apply
      (ProposedValues.childInputs (body signalType)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage) contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule signalType).Holds inputs contractState _
    rw [outputRule_holds_iff signalType]
    have boundaryOutput := boundary .value
    change outputs .value = (childProposals .storage).outputs .output at boundaryOutput
    exact boundaryOutput.trans ((Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have storageNextValue : storageNextState .stored =
        (ProposedValues.childInputs (body signalType)
          (fun child => (layerChildren child).moduleStructure)
          inputs childProposals .storage) .input := by
      rfl
    have selected := selectionEvaluates.1 Mux.Rule.select
    change (Mux.selectRule signalType).Holds _ SignalMap.emptyValues _ at selected
    simp [Contracts.Cycle.CycleOutputRule.Holds, Mux.selectRule, SignalSelection.Matches,
      SignalSelection.project, SignalMap.select, SignalSelection.prepend] at selected
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value
        else (childProposals .storage).outputs .output at selected
    have storageCurrent := (Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    simp only [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.apply,
      SignalSelection.project, SignalSelection.prepend, SignalMap.select]
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value else contractState .stored
    rw [selected, storageCurrent]

end LayerCertification

/-- The enabled-register wiring implements its contract for any mux and
register implementations satisfying their public contracts. -/
noncomputable opaque certifiedLayer (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body signalType)
      (childContracts signalType) (cycleContract signalType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType) (coversChildren signalType)
    (stateCorresponds signalType)
    (fun children structuralState =>
      (children .storage).certification.hasCorrespondingState
        (structuralState .storage))
    (implements signalType)

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (certifiedLayer signalType).certifyComposite
    (structuralChildren signalType) (certifiedChildren signalType)
    (by
      intro child
      cases child with
      | selection => exact Mux.certifiedStructure_moduleStructure signalType
      | storage => exact Register.certified_moduleStructure signalType)

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType).bundle

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal,
      (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState
end Silean.Modules.EnabledRegister
