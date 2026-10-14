import Silean.Modules.BarrelShifter.Internal.BarrelShifterStructure
import Silean.Semantics.StructuralRuleDerivation

/-! Contract-independent certification of the pipelined mux hierarchy. -/

namespace Silean.Modules.BarrelShifter.Internal

open Silean
open Silean.Authoring
open Silean.Modules

private abbrev wholeRules (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (Modules.BarrelShifter.body element exponent pipeline)

private abbrev stageOccurrence (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent)
    (stage : Fin exponent) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline) :=
  ⟨.stage stage, .apply⟩

private abbrev outputOccurrence (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline) :=
  ⟨.outputDelay, .apply⟩

private abbrev stageEnumeration (exponent : Nat) : Enumeration (Fin exponent) :=
  Enumeration.fin exponent

private abbrev priorAvailability (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) (stage : Fin exponent) :=
  ((stageEnumeration exponent).locate stage).preceding.reverse.map
    (stageOccurrence element exponent pipeline)

private theorem stageOccurrence_injective (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :
    Function.Injective (stageOccurrence element exponent pipeline) := by
  intro left right equal
  have childEqual := congrArg
    ModuleStructuralCertification.Layer.RuleOccurrence.child equal
  cases childEqual
  rfl

private theorem previousOutputAvailable (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent)
    (stage : Fin exponent) (nonzero : stage.val ≠ 0)
    (output : (Stage.ports element exponent).outputs.Label) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := Modules.BarrelShifter.body element exponent pipeline)
      (childRules := wholeRules element exponent pipeline)
      (fun _ => True)
      (priorAvailability element exponent pipeline stage)
      (SignalSource.instanceOutput
        (ports := (Modules.BarrelShifter.body
          element exponent pipeline).ports)
        (instancePorts := (Modules.BarrelShifter.body
          element exponent pipeline).instancePorts)
        (.stage (previousStage exponent stage)) output) := by
  refine ModuleStructuralCertification.Layer.sourceAvailable_of_instanceOutput
    (rule := ModuleStructuralRules.WholeRule.apply) ?_ ?_
  · apply ModuleStructuralCertification.Layer.Schedule.occurrence_mem_preceding_of_ordinal_lt
    change
      ((stageEnumeration exponent).ordinal
        (previousStage exponent stage)).val <
      ((stageEnumeration exponent).ordinal stage).val
    change
      (ListIndex.finRange (previousStage exponent stage)).toFin.val <
      (ListIndex.finRange stage).toFin.val
    simp only [ListIndex.finRange_toFin_val, previousStage]
    omega
  · let outputs := (Stage.ports element exponent).outputs
    exact (outputs.labels.locate output).mem

private theorem stageReadsAvailable (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent)
    (stage : Fin exponent)
    (input : (Stage.ports element exponent).inputs.Label)
    (member : input ∈
      (stageOccurrence element exponent pipeline stage).reads) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := Modules.BarrelShifter.body element exponent pipeline)
      (childRules := wholeRules element exponent pipeline)
      (fun _ => True)
      (priorAvailability element exponent pipeline stage)
      ((Modules.BarrelShifter.body element exponent pipeline).wiring
        |>.instanceInput (.stage stage) input) := by
  cases input <;> by_cases zero : stage.val = 0
  · simp only [Modules.BarrelShifter.wiring, dif_pos zero]
    trivial
  · simp only [Modules.BarrelShifter.wiring, dif_neg zero]
    exact previousOutputAvailable element exponent pipeline stage zero .shift
  · simp only [Modules.BarrelShifter.wiring, dif_pos zero]
    trivial
  · simp only [Modules.BarrelShifter.wiring, dif_neg zero]
    exact previousOutputAvailable element exponent pipeline stage zero .result

private theorem orderedNodup (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :
    ((stageEnumeration exponent).values.reverse.map
      (stageOccurrence element exponent pipeline)).Nodup :=
  List.nodup_map_of_injective _
    (stageOccurrence_injective element exponent pipeline)
    (List.nodup_reverse_of_nodup (stageEnumeration exponent).nodup)

private noncomputable def stageSchedule (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :=
  ModuleStructuralCertification.Layer.Schedule.callSequentialFamilyAfter
    (body := Modules.BarrelShifter.body element exponent pipeline)
    (childRules := wholeRules element exponent pipeline)
    (inputAvailable := fun _ => True)
    [] (stageEnumeration exponent)
    (stageOccurrence element exponent pipeline)
    (stageOccurrence_injective element exponent pipeline)
    (by simpa using orderedNodup element exponent pipeline)
    (fun stage input member => by
      simpa using stageReadsAvailable element exponent pipeline
        stage input member)

private theorem outputReadAvailable (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent)
    (port : (OptionalShiftRegister.ports
      (.vector (size exponent) element)).inputs.Label)
    (member : port ∈ (outputOccurrence element exponent pipeline).reads) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := Modules.BarrelShifter.body element exponent pipeline)
      (childRules := wholeRules element exponent pipeline)
      (fun _ => True)
      (stageSchedule element exponent pipeline).finalAvailability
      ((Modules.BarrelShifter.body element exponent pipeline).wiring
        |>.instanceInput .outputDelay port) := by
  cases port
  by_cases empty : exponent = 0
  · simp only [Modules.BarrelShifter.wiring, dif_pos empty]
    trivial
  · simp only [Modules.BarrelShifter.wiring, dif_neg empty]
    refine ModuleStructuralCertification.Layer.sourceAvailable_of_instanceOutput
      (rule := ModuleStructuralRules.WholeRule.apply) ?_ ?_
    · have finished := (stageSchedule element exponent pipeline).finished
      rw [finished]
      simp only [List.append_nil, List.mem_map, List.mem_reverse]
      exact ⟨lastStage exponent empty,
        (stageEnumeration exponent).locate (lastStage exponent empty) |>.mem,
        rfl⟩
    · let outputs := (Stage.ports element exponent).outputs
      exact (outputs.labels.locate (.result)).mem

private theorem outputFresh (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :
    outputOccurrence element exponent pipeline ∉
      (stageSchedule element exponent pipeline).finalAvailability := by
  intro member
  have finished := (stageSchedule element exponent pipeline).finished
  rw [finished] at member
  simp only [List.append_nil, List.mem_map, List.mem_reverse] at member
  rcases member with ⟨stage, _, equal⟩
  have childEqual := congrArg
    ModuleStructuralCertification.Layer.RuleOccurrence.child equal
  cases childEqual

private noncomputable def outputSchedule (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :
    ModuleStructuralCertification.Layer.Schedule
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline) (fun _ => True) (fun _ => True)
      (stageSchedule element exponent pipeline).finalAvailability :=
  .call (outputOccurrence element exponent pipeline)
    (outputReadAvailable element exponent pipeline)
    (outputFresh element exponent pipeline)
    (.done trivial)

private noncomputable def completeRuleSchedule (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :
    ModuleStructuralCertification.Layer.Schedule
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline) (fun _ => True) (fun _ => True) [] :=
  (stageSchedule element exponent pipeline).append
    (outputSchedule element exponent pipeline)

private theorem completeRuleSchedule_covers (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :
    ModuleStructuralCertification.Layer.CoversAllRules
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline)
      (completeRuleSchedule element exponent pipeline).finalAvailability := by
  intro child rule
  cases rule
  simp only [completeRuleSchedule,
    ModuleStructuralCertification.Layer.Schedule.finalAvailability_append,
    outputSchedule,
    ModuleStructuralCertification.Layer.Schedule.finalAvailability_call,
    ModuleStructuralCertification.Layer.Schedule.finalAvailability_done]
  cases child with
  | outputDelay => exact List.mem_cons_self
  | stage stage =>
      apply List.mem_cons_of_mem
      have finished := (stageSchedule element exponent pipeline).finished
      rw [finished]
      simp only [List.append_nil, List.mem_map, List.mem_reverse]
      exact ⟨stage, (stageEnumeration exponent).locate stage |>.mem, rfl⟩

private noncomputable def completeSchedule (element : SignalType)
    (exponent : Nat) (pipeline : Pipeline exponent) :
    ModuleStructuralCertification.Layer.ScheduleDerivation.DerivedCompleteSchedule
      (Modules.BarrelShifter.body element exponent pipeline)
      (wholeRules element exponent pipeline) where
  schedule := completeRuleSchedule element exponent pipeline
  coversAllRules := completeRuleSchedule_covers element exponent pipeline

private theorem childStructuralCertifications
    (element : SignalType) (exponent : Nat) (pipeline : Pipeline exponent) :
    ∀ child,
      ModuleStructuralCertification
        (Modules.BarrelShifter.structuralChildren
          element exponent pipeline child)
  | .stage stage =>
      Stage.structuralCertification element exponent stage
        (pipeline.registerBoundary stage.castSucc)
  | .outputDelay =>
      OptionalShiftRegister.structuralCertification
        (.vector (size exponent) element)
        (pipeline.registerBoundary (Fin.last exponent)).toNat

/-- The complete barrel shifter has exactly one structural solution for every
input and physical state, independently of its trace contract. -/
theorem structuralCertification (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :
    ModuleStructuralCertification
      (Modules.BarrelShifter.moduleStructure element exponent pipeline) :=
  (completeSchedule element exponent pipeline).certifyComposite
    (Modules.BarrelShifter.structuralChildren element exponent pipeline)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (Modules.BarrelShifter.body element exponent pipeline)
      (Modules.BarrelShifter.structuralChildren element exponent pipeline)
      (childStructuralCertifications element exponent pipeline))
    (fun _ => rfl)

end Silean.Modules.BarrelShifter.Internal
