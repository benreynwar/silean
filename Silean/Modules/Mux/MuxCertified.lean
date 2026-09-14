import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxContract
import Silean.Modules.Mux.Mux
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Primitives.Not

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-- Contract-facing selection law for the generic mux. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  exact (selectRule_holds_iff signalType inputs state outputs).mp
    (evaluates.1 Rule.select)


module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  invertSelect := Primitives.notCertified.certification,
  chooseFalse := Mask.certification signalType,
  chooseTrue := Mask.certification signalType,
  combine := BitwiseOr.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .select => [.invertSelect => Primitives.NotRule.apply,
      .chooseFalse => Mask.Rule.apply,
      .chooseTrue => Mask.Rule.apply,
      .combine => BitwiseOr.Rule.apply]
  state := []

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
  · simp [cycleContract, stateRule,
      Contracts.Cycle.CycleStateRule.apply]

end LayerCertification

module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signalType

end Silean.Modules.Mux

/-! Checked-authoring assessment (2026-09-13).

The author-facing construction is a short do-block. Exact correspondence is
`rfl`; the complete certificate adds name uniqueness. Naming normalization
requires two local three-case port-projection proofs and one small generic
transport lemma, not changes to structural types or downstream certification.
The three child-call wrappers are explicit boilerplate; no new macros are used.

Three fresh-process direct Lean checks with prebuilt imports took 1.34, 1.30,
and 1.27 seconds for the original combined authoring/proof file (median 1.30s). The independent description file
took 0.89, 0.88, and 0.86 seconds (median 0.88s). These are whole-file wall times,
including imports and the negative checks, not isolated kernel-proof timings.

Scope: arbitrary SignalType, but four fixed children. This does not establish
ergonomics for variable-sized child families. Descriptions preserve order as
well as names and retain actual NamedModules, rather than trusting module-key
strings. Existing children have noncomputable structures, so this example is
noncomputable too; equality is kernel checked, not a native executable test.
-/

namespace Silean.Modules.Mux.Description

open Silean Naming Authoring.CircuitDescription

private theorem maskPorts (signalType : SignalType) :
    (Mask.Naming.namingWith signalType (.positional _)).ports = Mask.Naming.ports signalType := by
  cases signalType with
  | bit =>
    rw [Mask.Naming.namingWith.eq_1]
    erw [ports_mpr_of_eq (Mask.moduleStructure.eq_1 .bit)]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_1
      Mask.interface Mask.bitModuleStructure)]
    rfl
  | vector length element =>
    rw [Mask.Naming.namingWith.eq_2]
    erw [ports_mpr_of_eq (Mask.moduleStructure.eq_1 (.vector length element))]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_2
      Mask.interface Mask.bitModuleStructure length element)]
    rfl
  | tuple fields =>
    rw [Mask.Naming.namingWith.eq_3]
    erw [ports_mpr_of_eq (Mask.moduleStructure.eq_1 (.tuple fields))]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_3
      Mask.interface Mask.bitModuleStructure fields)]
    rfl

private theorem binaryPorts [operation : Composition.BinaryLeafwise.Operation]
    [gate : Composition.BinaryLeafwise.BitGate operation]
    (family scope : String) (bitNaming : ModuleNaming gate.certified.moduleStructure)
    (signalType : SignalType) :
    (Naming.BinaryLeafwise.namingWith family scope bitNaming signalType (.positional _)).ports =
      Naming.BinaryLeafwise.ports signalType := by
  cases signalType with
  | bit =>
    rw [Naming.BinaryLeafwise.namingWith.eq_1]
    erw [ports_mpr_of_eq (Composition.BinaryLeafwise.moduleStructure.eq_1 .bit)]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_1
      Composition.BinaryLeafwise.interface Composition.BinaryLeafwise.bitModuleStructure)]
    rfl
  | vector length element =>
    rw [Naming.BinaryLeafwise.namingWith.eq_2]
    erw [ports_mpr_of_eq (Composition.BinaryLeafwise.moduleStructure.eq_1 (.vector length element))]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_2
      Composition.BinaryLeafwise.interface Composition.BinaryLeafwise.bitModuleStructure length element)]
    rfl
  | tuple fields =>
    rw [Naming.BinaryLeafwise.namingWith.eq_3]
    erw [ports_mpr_of_eq (Composition.BinaryLeafwise.moduleStructure.eq_1 (.tuple fields))]
    erw [ports_mpr_of_eq (Composition.LeafwiseInterface.moduleStructure.eq_3
      Composition.BinaryLeafwise.interface Composition.BinaryLeafwise.bitModuleStructure fields)]
    rfl

private theorem bitwiseOrPorts (signalType : SignalType) :
    (BitwiseOr.Naming.namingWith signalType (.positional _)).ports = BitwiseOr.Naming.ports signalType := by
  unfold BitwiseOr.Naming.namingWith BitwiseOr.Naming.ports BitwiseOr.Naming.portsWithNaming
  refine @binaryPorts ?_ ?_ ?_ ?_ ?_ signalType

theorem same (signalType : SignalType) :
    some (description signalType) = ofNaming (Mux.naming signalType) := by
  rfl

/-! Exact translation is reflexivity. Name uniqueness additionally uses the
port-projection lemmas above: production's recursive naming is transported
across structural equalities. `erw` is important there because the participating
structure definitions are not all reducible at the default rewrite transparency.
No alternate label representation or changed production declaration is needed.
-/
theorem boundaryNamesUnique (signalType : SignalType) :
    (((description signalType).inputs.map (·.name)) ++
      ((description signalType).outputs.map (·.port.name))).Nodup :=
  of_decide_eq_true rfl

theorem instanceNamesUnique (signalType : SignalType) :
    ((description signalType).children.map (·.name)).Nodup :=
  of_decide_eq_true rfl

theorem unique (signalType : SignalType) : (description signalType).UniqueNames := by
  refine ⟨boundaryNamesUnique signalType, instanceNamesUnique signalType, ?_⟩
  intro child member
  change child ∈ [_, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal <;> subst child <;>
    constructor <;> simp only [maskPorts, bitwiseOrPorts] <;>
    exact of_decide_eq_true rfl

theorem corresponds (signalType : SignalType) :
    Corresponds (description signalType) (Mux.naming signalType) :=
  ⟨same signalType, unique signalType⟩

/-! Small negative checks: the equality checks actual wiring, and uniqueness
is a real obligation rather than something assumed of every builder result. -/
theorem wrongOutputRejected (signalType : SignalType) :
    some { description signalType with outputs :=
      [⟨⟨"result", signalType⟩, .input "whenTrue"⟩] } ≠
        ofNaming (Mux.naming signalType) := by
  rw [← same signalType]
  intro equal
  have sources := congrArg (fun value : Option Description =>
    value.map fun circuit => circuit.outputs.map (·.source)) equal
  change some [Source.input "whenTrue"] =
    some [Source.child "combine" _] at sources
  cases sources

theorem duplicateInputRejected (signalType : SignalType) :
    ¬ ({ description signalType with inputs :=
      [⟨"select", .bit⟩, ⟨"select", .bit⟩] } : Description).UniqueNames := by
  intro names
  have distinct := names.1
  change ([SourceName.plain "select", SourceName.plain "select"] ++ _).Nodup at distinct
  simp at distinct

/-- Any structural realization of the authored description has production
Mux's certified selection behavior. The generic correspondence proof handles
all label changes; this proof simply applies the existing Mux contract law. -/
theorem result_of_corresponding_solution (signalType : SignalType)
    {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    {key : ModuleKey} {ports : ModulePortsNaming body.ports}
    {instanceName : body.instancePorts.Name → SourceName}
    {childNaming : (child : body.instancePorts.Name) → ModuleNaming (children child)}
    (translation : Corresponds (description signalType)
      (ModuleNaming.composite key ports instanceName childNaming))
    (inputs : body.ports.inputs.Values)
    (state : (ModuleStructure.composite body children).State)
    (proposal : ProposedValues (ModuleStructure.composite body children))
    (solution : (ModuleStructure.composite body children).IsSolution inputs state proposal) :
    ((translation.transferProposal (corresponds signalType) proposal).outputs .result) =
      bif (translation.transferInputs (corresponds signalType) inputs) .select then
        (translation.transferInputs (corresponds signalType) inputs) .whenTrue else
        (translation.transferInputs (corresponds signalType) inputs) .whenFalse := by
  obtain ⟨contractState, nextContractState, _, evaluates, _⟩ :=
    translation.certified_solution (corresponds signalType) (Mux.certification signalType)
      inputs state proposal solution
  exact Mux.result_of_evaluatesTo signalType _ contractState _ nextContractState evaluates

end Silean.Modules.Mux.Description
