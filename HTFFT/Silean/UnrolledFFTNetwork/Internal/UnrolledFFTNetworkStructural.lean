import HTFFT.Silean.UnrolledFFTNetwork.Internal.UnrolledFFTNetworkStructure
import Silean.Semantics.StructuralRuleDerivation

/-! Contract-independent certification of the unrolled-network hierarchy. -/

namespace HTFFT.Silean.UnrolledFFTNetwork

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

private abbrev wholeRules
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body depth configuration table)

private abbrev occurrence
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (child : Instance depth) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body depth configuration table)
      (wholeRules depth configuration table) :=
  ⟨child, .apply⟩

/-- Numeric position in the alternating dependency order.  Boundary `b`
occupies `2b`; layer `s` occupies `2s+1`. -/
private def schedulePosition : Instance depth → Fin (2 * depth + 1)
  | .boundaryDelay boundary => ⟨2 * boundary.val, by omega⟩
  | .layer stage => ⟨2 * stage.val + 1, by omega⟩

/-- Recover the child at one numeric dependency position. -/
private def scheduledInstance (position : Fin (2 * depth + 1)) :
    Instance depth :=
  if even : position.val % 2 = 0 then
    .boundaryDelay ⟨position.val / 2, by
      have remainder := Nat.mod_lt position.val (by omega : 0 < 2)
      have division := Nat.mod_add_div position.val 2
      omega⟩
  else
    .layer ⟨position.val / 2, by
      have remainder := Nat.mod_lt position.val (by omega : 0 < 2)
      have division := Nat.mod_add_div position.val 2
      omega⟩

private theorem scheduledInstance_leftInverse (depth : Nat) :
    Function.LeftInverse (@schedulePosition depth) (@scheduledInstance depth) := by
  intro position
  apply Fin.ext
  simp only [scheduledInstance]
  split
  next even =>
    simp only [schedulePosition]
    have remainder := Nat.mod_lt position.val (by omega : 0 < 2)
    have division := Nat.mod_add_div position.val 2
    omega
  next odd =>
    simp only [schedulePosition]
    have remainder := Nat.mod_lt position.val (by omega : 0 < 2)
    have division := Nat.mod_add_div position.val 2
    omega

private theorem scheduledInstance_rightInverse (depth : Nat) :
    Function.RightInverse (@schedulePosition depth) (@scheduledInstance depth) := by
  intro child
  cases child with
  | boundaryDelay boundary =>
      simp [schedulePosition, scheduledInstance]
  | layer stage =>
      simp [schedulePosition, scheduledInstance]
      apply Fin.ext
      simp [Nat.mul_add_div]

/-- Enumeration in dependency order: boundary zero, then each layer followed
by its successor boundary. -/
@[reducible] private def scheduleEnumeration (depth : Nat) :
    Enumeration (Instance depth) :=
  Enumeration.relabel (Enumeration.fin (2 * depth + 1))
    scheduledInstance schedulePosition
    (scheduledInstance_leftInverse depth)
    (scheduledInstance_rightInverse depth)

private theorem scheduleOrdinal_val (child : Instance depth) :
    ((scheduleEnumeration depth).ordinal child).val =
      (schedulePosition child).val := by
  let mapped := (ListIndex.finRange (schedulePosition child)).map scheduledInstance
  let inverse := scheduledInstance_rightInverse depth child
  let explicit : ListIndex child (scheduleEnumeration depth).values :=
    inverse ▸ mapped
  have equal := ListIndex.eq_of_nodup (scheduleEnumeration depth).nodup
    ((scheduleEnumeration depth).locate child) explicit
  change ((scheduleEnumeration depth).locate child).toFin.val =
    (schedulePosition child).val
  rw [equal]
  calc
    explicit.toFin.val = mapped.toFin.val :=
      ListIndex.toFin_val_transport inverse mapped
    _ = (schedulePosition child).val := by simp [mapped]

private theorem occurrence_injective
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    Function.Injective (occurrence depth configuration table) := by
  intro left right equal
  exact congrArg
    ModuleStructuralCertification.Layer.RuleOccurrence.child equal

private abbrev priorAvailability
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (child : Instance depth) :=
  ((scheduleEnumeration depth).locate child).preceding.reverse.map
    (occurrence depth configuration table)

private theorem earlierOutputAvailable
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (earlier later : Instance depth)
    (output : ((body depth configuration table).instancePorts.ports
      earlier).outputs.Label)
    (before : (schedulePosition earlier).val <
      (schedulePosition later).val) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := body depth configuration table)
      (childRules := wholeRules depth configuration table)
      (fun _ => True)
      (priorAvailability depth configuration table later)
      (.instanceOutput earlier output) := by
  refine ModuleStructuralCertification.Layer.sourceAvailable_of_instanceOutput
    (rule := ModuleStructuralRules.WholeRule.apply) ?_ ?_
  · apply ModuleStructuralCertification.Layer.Schedule.occurrence_mem_preceding_of_ordinal_lt
    change ((scheduleEnumeration depth).ordinal earlier).val <
      ((scheduleEnumeration depth).ordinal later).val
    simpa only [scheduleOrdinal_val] using before
  · change output ∈ ((body depth configuration table).instancePorts.ports
      earlier).outputs.labels.values
    let outputs := ((body depth configuration table).instancePorts.ports earlier).outputs
    exact (outputs.labels.locate output).mem

private theorem childReadsAvailable
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (child : Instance depth)
    (input : ((body depth configuration table).instancePorts.ports
      child).inputs.Label)
    (member : input ∈ (occurrence depth configuration table child).reads) :
    ModuleStructuralCertification.Layer.sourceAvailable
      (body := body depth configuration table)
      (childRules := wholeRules depth configuration table)
      (fun _ => True)
      (priorAvailability depth configuration table child)
      ((body depth configuration table).wiring.instanceInput child input) := by
  cases child with
  | layer stage =>
      cases input
      exact earlierOutputAvailable depth configuration table
        (.boundaryDelay stage.castSucc) (.layer stage) .output (by
          simp [schedulePosition])
  | boundaryDelay boundary =>
      cases input
      by_cases zero : boundary.val = 0
      · simp only [wiring, dif_pos zero,
          ModuleStructuralCertification.Layer.sourceAvailable_castType]
        trivial
      · simp only [wiring, dif_neg zero,
          ModuleStructuralCertification.Layer.sourceAvailable_castType]
        apply earlierOutputAvailable depth configuration table
          (.layer (Internal.previousStage boundary zero))
          (.boundaryDelay boundary) .output
        simp only [schedulePosition]
        simp only [Internal.previousStage]
        omega

private theorem orderedNodup
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ((scheduleEnumeration depth).values.reverse.map
      (occurrence depth configuration table)).Nodup :=
  List.nodup_map_of_injective _
    (occurrence_injective depth configuration table)
    (List.nodup_reverse_of_nodup (scheduleEnumeration depth).nodup)

private noncomputable def orderedSchedule
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :=
  ModuleStructuralCertification.Layer.Schedule.callSequentialFamilyAfter
    (body := body depth configuration table)
    (childRules := wholeRules depth configuration table)
    (inputAvailable := fun _ => True)
    [] (scheduleEnumeration depth)
    (occurrence depth configuration table)
    (occurrence_injective depth configuration table)
    (by simpa using orderedNodup depth configuration table)
    (fun child input member => by
      simpa using childReadsAvailable depth configuration table
        child input member)

private noncomputable def completeSchedule
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification.Layer.Schedule
      (body depth configuration table)
      (wholeRules depth configuration table)
      (fun _ => True) (fun _ => True) [] :=
  (orderedSchedule depth configuration table).mapFinish
    (fun _ _ => trivial)

private theorem completeSchedule_covers
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification.Layer.CoversAllRules
      (body depth configuration table)
      (wholeRules depth configuration table)
      (completeSchedule depth configuration table).finalAvailability := by
  intro child rule
  cases rule
  have finalEqual := (orderedSchedule depth configuration table).finished
  change occurrence depth configuration table child ∈
    (completeSchedule depth configuration table).finalAvailability
  simp only [completeSchedule,
    ModuleStructuralCertification.Layer.Schedule.finalAvailability_mapFinish]
  rw [finalEqual]
  simp only [List.mem_append, List.not_mem_nil, or_false,
    List.mem_map, List.mem_reverse]
  exact ⟨child, (scheduleEnumeration depth).locate child |>.mem, rfl⟩

private noncomputable def derivedCompleteSchedule
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification.Layer.ScheduleDerivation.DerivedCompleteSchedule
      (body depth configuration table)
      (wholeRules depth configuration table) where
  schedule := completeSchedule depth configuration table
  coversAllRules := completeSchedule_covers depth configuration table

private theorem childStructuralCertifications
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren depth configuration table child)
  | .boundaryDelay boundary =>
      OptionalShiftRegister.structuralCertification
        (Internal.samplesType configuration boundary)
        (configuration.boundaryLatency boundary)
  | .layer stage =>
      UnrolledFFTLayer.structuralCertification configuration table stage

/-- The complete unrolled network has exactly one structural solution for
every input and physical state. -/
theorem Internal.structuralCertification
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table) :=
  (derivedCompleteSchedule depth configuration table).certifyComposite
    (structuralChildren depth configuration table)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body depth configuration table)
      (structuralChildren depth configuration table)
      (childStructuralCertifications depth configuration table))
    (fun _ => rfl)

end HTFFT.Silean.UnrolledFFTNetwork
