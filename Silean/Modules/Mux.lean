import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.PrimitiveNaming
import Silean.Modules.Mask
import Silean.Modules.BitwiseOr
import Silean.Primitives.NotPrimitive

namespace Silean.Modules.Mux

open Silean
open Contracts.Cycle.Certification.Layer

/-! ## Hardware structure -/

/-- A generic combinational mux built from masking and bitwise OR. -/
inductive Instance
  /-- Produces the complement of the select bit. -/
  | invertSelect
  /-- Passes `whenFalse` only when select is low. -/
  | chooseFalse
  /-- Passes `whenTrue` only when select is high. -/
  | chooseTrue
  /-- Combines the two mutually exclusive masked values. -/
  | combine
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .invertSelect => Primitives.not.ports
    | .chooseFalse | .chooseTrue => Mask.ports signalType
    | .combine => BitwiseOr.ports signalType

inductive Input
  | select
  | whenFalse
  | whenTrue
deriving Enumeration

inductive Output
  | result
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .select => .bit
    | .whenFalse | .whenTrue => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .result => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- The combined masked branches are the mux result.
    | .result => c.instanceOutput .combine .result
    instanceInput := fun
    -- Generate the low-select mask.
    | .invertSelect, .input =>
        c.moduleInput .select
    -- Mask the false branch with the inverted select bit.
    | .chooseFalse, .value =>
        c.moduleInput .whenFalse
    | .chooseFalse, .mask =>
        c.instanceOutput .invertSelect .output
    -- Mask the true branch with the select bit.
    | .chooseTrue, .value =>
        c.moduleInput .whenTrue
    | .chooseTrue, .mask =>
        c.moduleInput .select
    -- OR the mutually exclusive branches.
    | .combine, .left =>
        c.instanceOutput .chooseFalse .result
    | .combine, .right =>
        c.instanceOutput .chooseTrue .result }

@[reducible] def body (signalType : SignalType) : ModuleBody where
  context := context signalType
  wiring := wiring signalType

end Silean.Modules.Mux

namespace Silean.Modules.Mux

open Silean

@[reducible] def childContracts (signalType : SignalType) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .invertSelect => Primitives.notCycleContract
  | .chooseFalse | .chooseTrue => Mask.cycleContract signalType
  | .combine => BitwiseOr.cycleContract signalType

@[reducible] noncomputable def certifiedChildren (signalType : SignalType) :
    (child : (instancePorts signalType).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure (childContracts signalType child)
  | .invertSelect =>
      ⟨.primitive Primitives.not, Primitives.notCertified.certification⟩
  | .chooseFalse | .chooseTrue =>
      ⟨Mask.moduleStructure signalType, (Mask.certified signalType).certification⟩
  | .combine =>
      ⟨BitwiseOr.moduleStructure signalType,
        (BitwiseOr.certified signalType).certification⟩

@[reducible] def structuralChildren (signalType : SignalType) :
    (name : (instancePorts signalType).Name) →
      ModuleStructure ((instancePorts signalType).ports name)
  | .invertSelect => Primitives.notCertified.moduleStructure
  | .chooseFalse | .chooseTrue => Mask.moduleStructure signalType
  | .combine => BitwiseOr.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (Modules.Mux.ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

end Silean.Modules.Mux

namespace Silean.Modules.Mux.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Mux.ports signalType) where
  inputs := ⟨fun
    | .select => "select"
    | .whenFalse => "when_false"
    | .whenTrue => "when_true"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .select => .bit
    | .whenFalse | .whenTrue => typeNaming
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.Mux.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.Mux.moduleStructure signalType) := by
  unfold Modules.Mux.moduleStructure
  exact .composite ⟨"mux", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun
      | .invertSelect => "invert_select"
      | .chooseFalse => "choose_false"
      | .chooseTrue => "choose_true"
      | .combine => "combine")
    (fun
      | .invertSelect => Silean.Naming.Primitive.not
      | .chooseFalse | .chooseTrue => Modules.Mask.Naming.namingWith signalType typeNaming
      | .combine => Modules.BitwiseOr.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Mux.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.Mux.Naming

namespace Silean.Modules.Mux

open Silean
open Contracts.Cycle.Certification.Layer

/-! ## Exact cycle behavior and certification -/

inductive Rule
  | select
deriving Enumeration

def selectRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (Modules.Mux.ports signalType) emptySignalMap
      { inputTypes := .cons .bit (.cons signalType (.cons signalType .nil))
        outputTypes := .cons signalType .nil } where
  readsInputs := ((Modules.Mux.inputMap signalType).select .whenTrue
    |>.prepend .whenFalse).prepend .select
  writesOutputs := (Modules.Mux.outputMap signalType).select .result
  target
    | (select, (whenFalse, (whenTrue, ()))), _ =>
        (bif select then whenTrue else whenFalse, ())

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (Modules.Mux.ports signalType) emptySignalMap :=
  Contracts.Cycle.CycleStateRule.empty (Modules.Mux.ports signalType)

def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (Modules.Mux.ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .select => ⟨_, selectRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

abbrev invertRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body signalType) (childContracts signalType) :=
  ⟨.invertSelect, Primitives.NotRule.apply⟩

abbrev falseRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body signalType) (childContracts signalType) :=
  ⟨.chooseFalse, Mask.Rule.apply⟩

abbrev trueRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body signalType) (childContracts signalType) :=
  ⟨.chooseTrue, Mask.Rule.apply⟩

abbrev combineRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body signalType) (childContracts signalType) :=
  ⟨.combine, BitwiseOr.Rule.apply⟩

private def scheduleOrders (signalType : SignalType) :
    ScheduleDerivation.RuleScheduleOrders (body signalType)
      (childContracts signalType) (cycleContract signalType) where
  output | .select => [invertRule signalType, falseRule signalType,
    trueRule signalType, combineRule signalType]
  state := []

private def derivedRuleSchedules (signalType : SignalType) :
    ScheduleDerivation.DerivedRuleSchedules (body signalType)
      (childContracts signalType) (cycleContract signalType) := by
  derive_rule_schedules (scheduleOrders signalType)

private abbrev ruleSchedules (signalType : SignalType) :=
  (derivedRuleSchedules signalType).schedules

private theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren :=
  (derivedRuleSchedules signalType).coversChildren

theorem selectRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (selectRule signalType).Holds inputs state outputs ↔
      outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, selectRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

mutual
  private theorem muxIdentity : ∀ (signalType : SignalType)
      (whenFalse whenTrue : signalType.Denote) (select : Bool),
      signalType.bitwiseOr
          (signalType.mask whenFalse (!select))
          (signalType.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .bit, whenFalse, whenTrue, select => by
        cases select <;> cases whenFalse <;> cases whenTrue <;> rfl
    | .vector _ element, whenFalse, whenTrue, select => by
        cases select <;>
        funext index
        · exact muxIdentity element (whenFalse index) (whenTrue index) false
        · exact muxIdentity element (whenFalse index) (whenTrue index) true
    | .tuple fields, whenFalse, whenTrue, select =>
        muxFieldsIdentity fields whenFalse whenTrue select

  private theorem muxFieldsIdentity : ∀ (fields : SignalTypes)
      (whenFalse whenTrue : fields.Denote) (select : Bool),
      fields.bitwiseOr
          (fields.mask whenFalse (!select))
          (fields.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .nil, (), (), _ => rfl
    | .cons head tail, (falseHead, falseTail), (trueHead, trueTail), select => by
        cases select
        · apply Prod.ext
          · exact muxIdentity head falseHead trueHead false
          · exact muxFieldsIdentity tail falseTail trueTail false
        apply Prod.ext
        · exact muxIdentity head falseHead trueHead true
        · exact muxFieldsIdentity tail falseTail trueTail true
end

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : (child : (instancePorts signalType).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signalType) layerChildren

private def stateCorresponds
    (_ : (cycleContract signalType).state.Values)
    (_ : (certificationStructure signalType layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure signalType layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton (child : Instance) :
      Subsingleton
        ((childContracts signalType child).state.Values) := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
        proposal satisfies child (by cases child <;> exact SignalMap.emptyValues)
  have invertEvaluates := (childMatch .invertSelect).1
  have falseEvaluates := (childMatch .chooseFalse).1
  have trueEvaluates := (childMatch .chooseTrue).1
  have combineEvaluates := (childMatch .combine).1
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change (selectRule signalType).Holds inputs contractState _
    rcases proposal with ⟨outputs, childProposals⟩
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (falseEvaluates.1 Mask.Rule.apply)
    have trueOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (trueEvaluates.1 Mask.Rule.apply)
    have combineOutput := (BitwiseOr.outputRule_holds_iff signalType _ _ _).mp
      (combineEvaluates.1 BitwiseOr.Rule.apply)
    have boundaryResult := boundary .result
    change outputs .result = (childProposals .combine).outputs .result at boundaryResult
    change (childProposals .chooseFalse).outputs .result =
      signalType.mask (inputs .whenFalse)
        ((childProposals .invertSelect).outputs .output) at falseOutput
    change (childProposals .chooseTrue).outputs .result =
      signalType.mask (inputs .whenTrue) (inputs .select) at trueOutput
    change (childProposals .combine).outputs .result =
      signalType.bitwiseOr ((childProposals .chooseFalse).outputs .result)
        ((childProposals .chooseTrue).outputs .result) at combineOutput
    rw [selectRule_holds_iff signalType]
    change outputs .result =
      bif inputs .select then inputs .whenTrue else inputs .whenFalse
    rw [boundaryResult, combineOutput, falseOutput, trueOutput, invertBit]
    exact muxIdentity signalType _ _ _
  · simp [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.empty,
      Contracts.Cycle.CycleStateRule.apply, SignalSelection.project]

end LayerCertification

noncomputable opaque certifiedLayer (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body signalType)
      (childContracts signalType) (cycleContract signalType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType) (coversChildren signalType)
    (stateCorresponds signalType) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (implements signalType)

noncomputable def certifiedStructure (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedStructure (cycleContract signalType) :=
  (certifiedLayer signalType).instantiate (certifiedChildren signalType)

@[simp] theorem certifiedStructure_moduleStructure (signalType : SignalType) :
    (certifiedStructure signalType).moduleStructure = moduleStructure signalType := by
  unfold certifiedStructure Contracts.Cycle.ModuleCycleCertifiedLayer.instantiate
    moduleStructure
  change ModuleStructure.composite (body signalType) (fun child =>
    (certifiedChildren signalType child).moduleStructure) =
      ModuleStructure.composite (body signalType) (structuralChildren signalType)
  congr
  funext child
  cases child <;> rfl

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (certifiedStructure signalType).certification.transportStructure
    (certifiedStructure_moduleStructure signalType)

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType).bundle

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

/-- Contract-facing selection law for the generic mux. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  have holds := evaluates.1 Rule.select
  change (selectRule signalType).Holds inputs state outputs at holds
  simpa [selectRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.Matches, SignalSelection.project, SignalSelection.prepend,
    SignalMap.select] using holds

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal, (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState

end Silean.Modules.Mux
