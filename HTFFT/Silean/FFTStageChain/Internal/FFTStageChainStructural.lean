import HTFFT.Silean.FFTStageChain.Internal.FFTStageChainStructure
import Silean.Semantics.StructuralRuleDerivation

/-! Contract-independent certification of the concrete rolled-stage chain. -/

namespace HTFFT.Silean.FFTStageChain
open FFT

open _root_.Silean
open _root_.Silean.Authoring

private abbrev wholeRules
    (depth : Nat) (configuration : Configuration depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration)

private abbrev occurrence
    (depth : Nat) (configuration : Configuration depth)
    (index : StageIndex configuration) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration)
      (wholeRules depth configuration) :=
  ⟨.stage index, .apply⟩

private abbrev stageEnumeration
    (configuration : Configuration depth) :
    Enumeration (StageIndex configuration) :=
  Enumeration.fin (stageCount depth configuration)

private abbrev priorAvailability
    (depth : Nat) (configuration : Configuration depth)
    (index : StageIndex configuration) :=
  ((stageEnumeration configuration).locate index).preceding.reverse.map
    (occurrence depth configuration)

private theorem occurrence_injective
    (depth : Nat) (configuration : Configuration depth) :
    Function.Injective (occurrence depth configuration) := by
  intro left right equal
  have childEqual := congrArg
    ModuleStructuralCertification.Layer.RuleOccurrence.child equal
  cases childEqual
  rfl

private theorem previousOutputAvailable
    (depth : Nat) (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0)
    (output : ((body depth configuration).instancePorts.ports
      (.stage (Internal.previousIndex configuration index nonzero))).outputs.Label) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := body depth configuration)
      (childRules := wholeRules depth configuration)
      (fun _ => True)
      (priorAvailability depth configuration index)
      (SignalSource.instanceOutput
        (ports := (body depth configuration).ports)
        (instancePorts := (body depth configuration).instancePorts)
        (.stage (Internal.previousIndex configuration index nonzero))
        output) := by
  refine ModuleStructuralCertification.Layer.sourceAvailable_of_instanceOutput
    (rule := ModuleStructuralRules.WholeRule.apply) ?_ ?_
  · apply ModuleStructuralCertification.Layer.Schedule.occurrence_mem_preceding_of_ordinal_lt
    change
      ((stageEnumeration configuration).ordinal
        (Internal.previousIndex configuration index nonzero)).val <
      ((stageEnumeration configuration).ordinal index).val
    change
      (ListIndex.finRange
        (Internal.previousIndex configuration index nonzero)).toFin.val <
      (ListIndex.finRange index).toFin.val
    simp only [ListIndex.finRange_toFin_val, Internal.previousIndex]
    omega
  · let outputs := ((body depth configuration).instancePorts.ports
      (.stage (Internal.previousIndex configuration index nonzero))).outputs
    exact (outputs.labels.locate output).mem

private theorem childReadsAvailable
    (depth : Nat) (configuration : Configuration depth)
    (index : StageIndex configuration)
    (input : ((body depth configuration).instancePorts.ports
      (.stage index)).inputs.Label)
    (member : input ∈
      (occurrence depth configuration index).reads) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := body depth configuration)
      (childRules := wholeRules depth configuration)
      (fun _ => True)
      (priorAvailability depth configuration index)
      ((body depth configuration).wiring.instanceInput (.stage index)
        input) := by
  cases input <;> by_cases zero : index.val = 0
  · simp only [wiring, dif_pos zero]
    trivial
  · simp only [wiring, dif_neg zero]
    exact previousOutputAvailable depth configuration index zero .o_first
  · simp only [wiring, dif_pos zero,
      ModuleStructuralCertification.Layer.sourceAvailable_castType]
    trivial
  · simp only [wiring, dif_neg zero,
      ModuleStructuralCertification.Layer.sourceAvailable_castType]
    exact previousOutputAvailable depth configuration index zero .o_data

private theorem orderedNodup
    (depth : Nat) (configuration : Configuration depth) :
    ((stageEnumeration configuration).values.reverse.map
      (occurrence depth configuration)).Nodup :=
  List.nodup_map_of_injective _
    (occurrence_injective depth configuration)
    (List.nodup_reverse_of_nodup (stageEnumeration configuration).nodup)

private noncomputable def orderedSchedule
    (depth : Nat) (configuration : Configuration depth) :=
  ModuleStructuralCertification.Layer.Schedule.callSequentialFamilyAfter
    (body := body depth configuration)
    (childRules := wholeRules depth configuration)
    (inputAvailable := fun _ => True)
    [] (stageEnumeration configuration)
    (occurrence depth configuration)
    (occurrence_injective depth configuration)
    (by simpa using orderedNodup depth configuration)
    (fun index input member => by
      simpa using childReadsAvailable depth configuration
        index input member)

private noncomputable def completeSchedule
    (depth : Nat) (configuration : Configuration depth) :
    ModuleStructuralCertification.Layer.Schedule
      (body depth configuration)
      (wholeRules depth configuration)
      (fun _ => True) (fun _ => True) [] :=
  (orderedSchedule depth configuration).mapFinish
    (fun _ _ => trivial)

private theorem completeSchedule_covers
    (depth : Nat) (configuration : Configuration depth) :
    ModuleStructuralCertification.Layer.CoversAllRules
      (body depth configuration)
      (wholeRules depth configuration)
      (completeSchedule depth configuration).finalAvailability := by
  intro child rule
  cases child with
  | stage index =>
      cases rule
      have finalEqual := (orderedSchedule depth configuration).finished
      change occurrence depth configuration index ∈
        (completeSchedule depth configuration).finalAvailability
      simp only [completeSchedule,
        ModuleStructuralCertification.Layer.Schedule.finalAvailability_mapFinish]
      rw [finalEqual]
      simp only [List.mem_append, List.not_mem_nil, or_false,
        List.mem_map, List.mem_reverse]
      exact ⟨index, (stageEnumeration configuration).locate index |>.mem, rfl⟩

private noncomputable def derivedCompleteSchedule
    (depth : Nat) (configuration : Configuration depth) :
    ModuleStructuralCertification.Layer.ScheduleDerivation.DerivedCompleteSchedule
      (body depth configuration)
      (wholeRules depth configuration) where
  schedule := completeSchedule depth configuration
  coversAllRules := completeSchedule_covers depth configuration

private theorem childStructuralCertifications
    (depth : Nat) (configuration : Configuration depth) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren depth configuration child)
  | .stage index =>
      FFTStage.structuralCertification configuration.arithmetic configuration.twiddleTable
        (stageGeometry configuration index)
        (configuration.rolledButterflyPipeline index)
        (configuration.rolledTwiddleDefinitionName index)

/-- The concrete rolled-stage chain has exactly one structural solution for
every boundary input and physical state. -/
theorem Internal.structuralCertification
    (depth : Nat) (configuration : Configuration depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration) :=
  (derivedCompleteSchedule depth configuration).certifyComposite
    (structuralChildren depth configuration)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration)
      (structuralChildren depth configuration)
      (childStructuralCertifications depth configuration))
    (fun _ => rfl)

end HTFFT.Silean.FFTStageChain
