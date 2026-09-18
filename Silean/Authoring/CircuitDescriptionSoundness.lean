import Silean.Authoring.CircuitDescription
import Silean.Semantics.StructuralEquations
import Silean.Contracts.Cycle.CycleImplementation

/-! Soundness of the named translation boundary. This file reasons about
production endpoints and structural equations; it does not define another
hardware interpreter.

`Corresponds.transferSolution_iff` is the main theorem: any two production
realizations certified against the same description have corresponding
structural solutions. Their label types may differ. The input/output/child
bijections preserve full entries, including child modules and all connections;
they are derived from the certificates, not supplied by an author. A complete
`HierStep` is transferred as one value, so its boundary values, recursive child
assignments, and derived structural state cannot drift apart.

Verification (2026-09-13): the final theorems use only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; there are no admitted proofs or
new axioms. Choice constructs proof-level label correspondences, not executable
hardware. Three fresh-process checks with prebuilt imports took 1.29/1.23/1.25s
for this file (median 1.25s), and 1.24/1.30/1.36s for the Mux mapping proofs
(median 1.30s, before merging them into `Internal/MuxVerification.lean`). These
are whole-file wall times including imports, not isolated
kernel timings. Production structure, semantics, and certification files were
not modified.
-/
namespace Silean.Authoring.CircuitDescription

open Silean Naming

/-- Duplicate-free keys make a named list lossless on its entries. -/
theorem namedEntry_unique {α : Type u} {β : Type v} (key : α → β)
    {entries : List α} (unique : (entries.map key).Nodup)
    {left right : α} (leftMem : left ∈ entries) (rightMem : right ∈ entries)
    (same : key left = key right) : left = right := by
  induction entries with
  | nil => cases leftMem
  | cons head tail induction =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMem with leftEqual | leftTail
    · subst left
      rcases List.mem_cons.mp rightMem with rightEqual | rightTail
      · exact rightEqual.symm
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMem with rightEqual | rightTail
      · subst right
        exact False.elim (distinct.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact induction distinct.2 leftTail rightTail

theorem enumeration_name_injective (enumeration : Enumeration α) (name : α → β)
    (unique : (enumeration.values.map name).Nodup) :
    ∀ {left right}, name left = name right → left = right := by
  intro left right same
  exact namedEntry_unique name unique (enumeration.locate left).mem
    (enumeration.locate right).mem same

/-- Include the signal type when comparing endpoints: name equality must not
silently identify endpoints of different types. -/
def packedSourceDescription {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child))
    (source : (signalType : SignalType) × SignalSource body.ports body.instancePorts signalType) :
    Source := sourceDescription ports instanceName childPorts source.2

theorem packedSourceDescription_injective {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child))
    (inputsUnique : ports.inputs.names.Nodup)
    (instancesUnique : (body.instancePorts.names.values.map instanceName).Nodup)
    (outputsUnique : ∀ child, (childPorts child).outputs.names.Nodup)
    {left right : (signalType : SignalType) ×
      SignalSource body.ports body.instancePorts signalType}
    (same : packedSourceDescription ports instanceName childPorts left =
      packedSourceDescription ports instanceName childPorts right) : left = right := by
  rcases left with ⟨_, left⟩
  rcases right with ⟨_, right⟩
  cases left with
  | moduleInput left =>
    cases right with
    | moduleInput right =>
      have names := Source.input.inj same
      have equal := enumeration_name_injective body.ports.inputs.labels
        ports.inputs.name inputsUnique names
      cases equal
      rfl
    | instanceOutput child port => cases same
  | instanceOutput leftChild leftPort =>
    cases right with
    | moduleInput right => cases same
    | instanceOutput rightChild rightPort =>
      have names := Source.child.inj same
      have equal := enumeration_name_injective body.instancePorts.names
        instanceName instancesUnique names.1
      cases equal
      have portEqual := enumeration_name_injective
        (body.instancePorts.ports leftChild).outputs.labels
        (childPorts leftChild).outputs.name (outputsUnique leftChild) names.2
      cases portEqual
      rfl

/-- In particular, equal named drivers of a fixed type are equal production
drivers, not merely drivers that happen to produce the same Boolean value. -/
theorem sourceDescription_injective {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child))
    (inputsUnique : ports.inputs.names.Nodup)
    (instancesUnique : (body.instancePorts.names.values.map instanceName).Nodup)
    (outputsUnique : ∀ child, (childPorts child).outputs.names.Nodup)
    {left right : SignalSource body.ports body.instancePorts signalType}
    (same : sourceDescription ports instanceName childPorts left =
      sourceDescription ports instanceName childPorts right) : left = right := by
  have packed := packedSourceDescription_injective ports instanceName childPorts
    inputsUnique instancesUnique outputsUnique
    (left := ⟨signalType, left⟩) (right := ⟨signalType, right⟩) same
  exact eq_of_heq (Sigma.mk.inj packed).2

/-- This uses the existing production source evaluator. No alternate
interpretation of the named description is introduced. -/
theorem sourceDescription_value_eq {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child))
    (inputsUnique : ports.inputs.names.Nodup)
    (instancesUnique : (body.instancePorts.names.values.map instanceName).Nodup)
    (outputsUnique : ∀ child, (childPorts child).outputs.names.Nodup)
    {left right : SignalSource body.ports body.instancePorts signalType}
    (same : sourceDescription ports instanceName childPorts left =
      sourceDescription ports instanceName childPorts right)
    (inputs : body.ports.inputs.Values)
    (childOutputs : (child : body.instancePorts.Name) →
      (body.instancePorts.ports child).outputs.Values) :
    left.value inputs childOutputs = right.value inputs childOutputs := by
  rw [sourceDescription_injective ports instanceName childPorts
    inputsUnique instancesUnique outputsUnique same]


/-- The existing certificate supplies all the source-uniqueness hypotheses;
no additional naming invariant is assumed by the endpoint soundness proof. -/
theorem Corresponds.source_names_unique {description : Description} {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    {key : ModuleKey} {ports : ModulePortsNaming body.ports}
    {instanceName : body.instancePorts.Name → SourceName}
    {childNaming : (child : body.instancePorts.Name) → ModuleNaming (children child)}
    (certificate : Corresponds description
      (ModuleNaming.composite key ports instanceName childNaming)) :
    ports.inputs.names.Nodup ∧
      (body.instancePorts.names.values.map instanceName).Nodup ∧
      ∀ child, (childNaming child).ports.outputs.names.Nodup := by
  have equal := Option.some.inj certificate.same
  have unique := certificate.unique
  rw [equal] at unique
  refine ⟨?_, ?_, ?_⟩
  · have boundary := (List.nodup_append.mp unique.1).1
    simpa only [portList, List.map_map, Function.comp_def, SignalMapNaming.names] using boundary
  · simpa only [List.map_map, Function.comp_def] using unique.2.1
  · intro child
    have member := List.mem_map_of_mem (f := fun child =>
      ({ name := instanceName child
         module := ⟨body.instancePorts.ports child, children child, childNaming child⟩
         inputs := (body.instancePorts.ports child).inputs.labels.values.map fun port =>
           ⟨⟨(childNaming child).ports.inputs.name port,
             (body.instancePorts.ports child).inputs.signalType port⟩,
             sourceDescription ports instanceName (fun child => (childNaming child).ports)
               (body.wiring.instanceInput child port)⟩ } : Child))
      (body.instancePorts.names.locate child).mem
    have childUnique := (unique.2.2 _ member).1
    exact (List.nodup_append.mp childUnique).2.1


/-- A proof-level correspondence, constructed from the compared descriptions.
Authors do not supply a label map, and matching preserves full entries. -/
structure EntryBijection {α : Type u} {β : Type v} {γ : Type w}
    (left : α → γ) (right : β → γ) where
  forward : α → β
  backward : β → α
  backward_forward : ∀ label, backward (forward label) = label
  forward_backward : ∀ label, forward (backward label) = label
  preserves : ∀ label, left label = right (forward label)

theorem EntryBijection.backward_preserves {left : α → γ} {right : β → γ}
    (bijection : EntryBijection left right) (label : β) :
    left (bijection.backward label) = right label := by
  rw [bijection.preserves, bijection.forward_backward]

/-- Transfer dependent data (port values, child states, or child assignments)
along the automatically constructed entry correspondence. -/
def EntryBijection.transfer {α : Type u} {β : Type v} {γ : Type w}
    {left : α → γ} {right : β → γ} (bijection : EntryBijection left right)
    (Value : γ → Type x) (values : (label : α) → Value (left label)) :
    (label : β) → Value (right label) :=
  fun label => cast (congrArg Value (bijection.backward_preserves label))
    (values (bijection.backward label))

theorem EntryBijection.transfer_forward {α : Type u} {β : Type v} {γ : Type w}
    {left : α → γ} {right : β → γ} (bijection : EntryBijection left right)
    (Value : γ → Type x) (values : (label : α) → Value (left label)) (label : α) :
    HEq (bijection.transfer Value values (bijection.forward label)) (values label) := by
  have equal := congrArg (fun label => (⟨left label, values label⟩ : Sigma Value))
    (bijection.backward_forward label)
  exact (cast_heq _ _).trans (Sigma.mk.inj equal).2

def EntryBijection.symm {left : α → γ} {right : β → γ}
    (bijection : EntryBijection left right) : EntryBijection right left where
  forward := bijection.backward
  backward := bijection.forward
  backward_forward := bijection.forward_backward
  forward_backward := bijection.backward_forward
  preserves := fun label => (bijection.backward_preserves label).symm

/-- The dependent transfer covers every target valuation. This applies equally
to boundary values, child states, and child assignments; preservation is not
restricted to a proper subset of target data. -/
theorem EntryBijection.transfer_surjective {α : Type u} {β : Type v} {γ : Type w}
    {left : α → γ} {right : β → γ} (bijection : EntryBijection left right)
    (Value : γ → Type x) (target : (label : β) → Value (right label)) :
    ∃ source, bijection.transfer Value source = target := by
  refine ⟨bijection.symm.transfer Value target, ?_⟩
  funext label
  exact eq_of_heq ((cast_heq _ _).trans (bijection.symm.transfer_forward Value target label))

/-- Equal named lists give a bijection even when their label types differ.
Uniqueness of names, not an assumed relationship between label constructors,
provides the inverse laws. -/
noncomputable def matchingEntries {α : Type u} {β : Type v} {γ : Type w}
    (leftLabels : Enumeration α) (rightLabels : Enumeration β)
    (left : α → γ) (right : β → γ) (name : γ → SourceName)
    (same : leftLabels.values.map left = rightLabels.values.map right)
    (unique : ((leftLabels.values.map left).map name).Nodup) :
    EntryBijection left right := by
  classical
  have rightUnique : ((rightLabels.values.map right).map name).Nodup := same ▸ unique
  have leftInjective : ∀ {a b}, left a = left b → a = b := by
    intro a b equal
    apply enumeration_name_injective leftLabels (name ∘ left)
      (by simpa only [List.map_map] using unique)
    exact congrArg name equal
  have rightInjective : ∀ {a b}, right a = right b → a = b := by
    intro a b equal
    apply enumeration_name_injective rightLabels (name ∘ right)
      (by simpa only [List.map_map] using rightUnique)
    exact congrArg name equal
  have rightExists (label : α) : ∃ other, right other = left label := by
    have member := List.mem_map_of_mem (f := left) (leftLabels.locate label).mem
    rw [same] at member
    rcases List.mem_map.mp member with ⟨other, _, equal⟩
    exact ⟨other, equal⟩
  have leftExists (label : β) : ∃ other, left other = right label := by
    have member := List.mem_map_of_mem (f := right) (rightLabels.locate label).mem
    rw [← same] at member
    rcases List.mem_map.mp member with ⟨other, _, equal⟩
    exact ⟨other, equal⟩
  let forward := fun label => Classical.choose (rightExists label)
  let backward := fun label => Classical.choose (leftExists label)
  have forwardEqual (label) : right (forward label) = left label :=
    Classical.choose_spec (rightExists label)
  have backwardEqual (label) : left (backward label) = right label :=
    Classical.choose_spec (leftExists label)
  exact {
    forward := forward
    backward := backward
    backward_forward := fun label => leftInjective
      ((backwardEqual (forward label)).trans (forwardEqual label))
    forward_backward := fun label => rightInjective
      ((forwardEqual (backward label)).trans (backwardEqual label))
    preserves := fun label => (forwardEqual label).symm }

/-- The concrete entries already stored by `ofNaming`. These abbreviations
only expose its fields to the proof; they do not introduce another encoding. -/
abbrev inputEntry (signals : SignalMap) (names : SignalMapNaming signals)
    (label : signals.Label) : Port := ⟨names.name label, signals.signalType label⟩

abbrev outputEntry {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child))
    (label : body.ports.outputs.Label) : Connection :=
  ⟨inputEntry body.ports.outputs ports.outputs label,
    sourceDescription ports instanceName childPorts (body.wiring.moduleOutput label)⟩

abbrev childEntry {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) → ModuleNaming (children child))
    (child : body.instancePorts.Name) : Child :=
  { name := instanceName child
    module := ⟨body.instancePorts.ports child, children child, childNaming child⟩
    inputs := (body.instancePorts.ports child).inputs.labels.values.map fun port =>
      ⟨inputEntry (body.instancePorts.ports child).inputs (childNaming child).ports.inputs port,
        sourceDescription ports instanceName (fun child => (childNaming child).ports)
          (body.wiring.instanceInput child port)⟩ }

/-- Equal actual children and corresponding hierarchy assignments have corresponding
output values. This inspects neither the child implementation nor its proof. -/
theorem namedModule_output_heq (left right : NamedModule) (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (stepsEqual : HEq leftStep rightStep)
    (unique : left.naming.ports.outputs.names.Nodup)
    (leftPort : left.ports.outputs.Label) (rightPort : right.ports.outputs.Label)
    (namesEqual : left.naming.ports.outputs.name leftPort =
      right.naming.ports.outputs.name rightPort) :
    HEq (leftStep.outputs leftPort) (rightStep.outputs rightPort) := by
  cases same
  have equal := eq_of_heq stepsEqual
  cases equal
  have portEqual := enumeration_name_injective left.ports.outputs.labels
    left.naming.ports.outputs.name unique namesEqual
  cases portEqual
  rfl

/-- Recover a child input's driver from equality of its full input table.
The child module itself is equal, so no arbitrary port renaming is permitted. -/
theorem namedModule_input_source_eq (left right : NamedModule) (same : left = right)
    (leftSource : left.ports.inputs.Label → Source)
    (rightSource : right.ports.inputs.Label → Source)
    (sameInputs : (left.ports.inputs.labels.values.map fun port =>
        (⟨inputEntry left.ports.inputs left.naming.ports.inputs port, leftSource port⟩ : Connection)) =
      (right.ports.inputs.labels.values.map fun port =>
        (⟨inputEntry right.ports.inputs right.naming.ports.inputs port, rightSource port⟩ : Connection)))
    (unique : left.naming.ports.inputs.names.Nodup)
    (leftPort : left.ports.inputs.Label) (rightPort : right.ports.inputs.Label)
    (sameName : left.naming.ports.inputs.name leftPort = right.naming.ports.inputs.name rightPort) :
    leftSource leftPort = rightSource rightPort := by
  cases same
  have equal := enumeration_name_injective left.ports.inputs.labels
    left.naming.ports.inputs.name unique sameName
  cases equal
  exact congrArg Connection.source ((List.map_inj_left.mp sameInputs)
    leftPort (left.ports.inputs.labels.locate leftPort).mem)

theorem namedModule_inputs_heq (left right : NamedModule) (same : left = right)
    (leftInputs : left.ports.inputs.Values) (rightInputs : right.ports.inputs.Values)
    (agree : ∀ leftPort rightPort,
      left.naming.ports.inputs.name leftPort = right.naming.ports.inputs.name rightPort →
      HEq (leftInputs leftPort) (rightInputs rightPort)) : HEq leftInputs rightInputs := by
  cases same
  apply heq_of_eq
  funext port
  exact eq_of_heq (agree port port rfl)

theorem namedModule_hierStep_inputs_heq (left right : NamedModule)
    (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (sameStep : HEq leftStep rightStep) :
    HEq leftStep.inputs rightStep.inputs := by
  cases same
  cases eq_of_heq sameStep
  rfl

theorem namedModule_solution_iff (left right : NamedModule) (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (stepEqual : HEq leftStep rightStep) :
    left.moduleStructure.IsSolution leftStep ↔
      right.moduleStructure.IsSolution rightStep := by
  cases same
  cases eq_of_heq stepEqual
  rfl

/-- Name-aligned production valuations give the same value to corresponding
sources, even across different boundary and instance-label types. The
bijections above are what will supply the alignment, rather than an author
assumption or a second interpreter. -/
theorem sourceDescription_value_heq
    {leftBody rightBody : ModuleBody}
    (leftPorts : ModulePortsNaming leftBody.ports)
    (rightPorts : ModulePortsNaming rightBody.ports)
    (leftName : leftBody.instancePorts.Name → SourceName)
    (rightName : rightBody.instancePorts.Name → SourceName)
    (leftChildPorts : (child : leftBody.instancePorts.Name) →
      ModulePortsNaming (leftBody.instancePorts.ports child))
    (rightChildPorts : (child : rightBody.instancePorts.Name) →
      ModulePortsNaming (rightBody.instancePorts.ports child))
    (leftInputs : leftBody.ports.inputs.Values)
    (rightInputs : rightBody.ports.inputs.Values)
    (leftOutputs : (child : leftBody.instancePorts.Name) →
      (leftBody.instancePorts.ports child).outputs.Values)
    (rightOutputs : (child : rightBody.instancePorts.Name) →
      (rightBody.instancePorts.ports child).outputs.Values)
    (inputsAgree : ∀ left right, leftPorts.inputs.name left = rightPorts.inputs.name right →
      HEq (leftInputs left) (rightInputs right))
    (outputsAgree : ∀ leftChild rightChild leftPort rightPort,
      leftName leftChild = rightName rightChild →
      (leftChildPorts leftChild).outputs.name leftPort =
        (rightChildPorts rightChild).outputs.name rightPort →
      HEq (leftOutputs leftChild leftPort) (rightOutputs rightChild rightPort))
    {leftType rightType : SignalType}
    (left : SignalSource leftBody.ports leftBody.instancePorts leftType)
    (right : SignalSource rightBody.ports rightBody.instancePorts rightType)
    (same : sourceDescription leftPorts leftName leftChildPorts left =
      sourceDescription rightPorts rightName rightChildPorts right) :
    HEq (left.value leftInputs leftOutputs) (right.value rightInputs rightOutputs) := by
  cases left with
  | moduleInput left =>
    cases right with
    | moduleInput right => exact inputsAgree left right (Source.input.inj same)
    | instanceOutput child port => cases same
  | instanceOutput leftChild leftPort =>
    cases right with
    | moduleInput right => cases same
    | instanceOutput rightChild rightPort =>
      exact outputsAgree leftChild rightChild leftPort rightPort
        (Source.child.inj same).1 (Source.child.inj same).2

theorem EntryBijection.forall_iff {left : α → γ} {right : β → γ}
    (bijection : EntryBijection left right) (P : α → Prop) (Q : β → Prop)
    (atLabel : ∀ label, P label ↔ Q (bijection.forward label)) :
    (∀ label, P label) ↔ ∀ label, Q label := by
  constructor
  · intro holds label
    have transported := (atLabel (bijection.backward label)).mp (holds _)
    simpa only [bijection.forward_backward] using transported
  · intro holds label
    exact (atLabel label).mpr (holds _)

theorem equality_iff_of_heq {α β : Sort u} {leftValue leftSource : α}
    {rightValue rightSource : β}
    (values : HEq leftValue rightValue) (sources : HEq leftSource rightSource) :
    (leftValue = leftSource) ↔ (rightValue = rightSource) := by
  cases values
  cases sources
  rfl

section Comparison

variable {description : Description} {leftBody rightBody : ModuleBody}
  {leftChildren : (child : leftBody.instancePorts.Name) →
    ModuleStructure (leftBody.instancePorts.ports child)}
  {rightChildren : (child : rightBody.instancePorts.Name) →
    ModuleStructure (rightBody.instancePorts.ports child)}
  {leftKey rightKey : ModuleKey}
  {leftPorts : ModulePortsNaming leftBody.ports}
  {rightPorts : ModulePortsNaming rightBody.ports}
  {leftName : leftBody.instancePorts.Name → SourceName}
  {rightName : rightBody.instancePorts.Name → SourceName}
  {leftNaming : (child : leftBody.instancePorts.Name) → ModuleNaming (leftChildren child)}
  {rightNaming : (child : rightBody.instancePorts.Name) → ModuleNaming (rightChildren child)}
  (leftCertificate : Corresponds description
    (ModuleNaming.composite leftKey leftPorts leftName leftNaming))
  (rightCertificate : Corresponds description
    (ModuleNaming.composite rightKey rightPorts rightName rightNaming))

/-- Complete parent-input correspondence: names and signal types are preserved
even though the two structural boundaries may use different label types. -/
noncomputable def Corresponds.inputBijection :
    EntryBijection (inputEntry leftBody.ports.inputs leftPorts.inputs)
      (inputEntry rightBody.ports.inputs rightPorts.inputs) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.ports.inputs.labels rightBody.ports.inputs.labels
    _ _ Port.name (congrArg Description.inputs descriptions)
  simpa only [List.map_map, Function.comp_def, inputEntry, SignalMapNaming.names]
    using leftCertificate.source_names_unique.1

/-- Parent-output correspondence preserves the driven source as well as the
port name and type. -/
noncomputable def Corresponds.outputBijection :
    EntryBijection (outputEntry leftPorts leftName (fun child => (leftNaming child).ports))
      (outputEntry rightPorts rightName (fun child => (rightNaming child).ports)) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.ports.outputs.labels rightBody.ports.outputs.labels
    _ _ (fun entry => entry.port.name) (congrArg Description.outputs descriptions)
  have unique := leftCertificate.unique.1
  rw [Option.some.inj leftCertificate.same] at unique
  exact (List.nodup_append.mp unique).2.1

/-- Child correspondence preserves the full NamedModule and every input
connection, not just the child's name or interface. -/
noncomputable def Corresponds.childBijection :
    EntryBijection (childEntry leftPorts leftName leftNaming)
      (childEntry rightPorts rightName rightNaming) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.instancePorts.names rightBody.instancePorts.names
    _ _ Child.name (congrArg Description.children descriptions)
  have unique := leftCertificate.unique.2.1
  rw [Option.some.inj leftCertificate.same] at unique
  exact unique

noncomputable def Corresponds.transferInputs (inputs : leftBody.ports.inputs.Values) :
    rightBody.ports.inputs.Values :=
  (leftCertificate.inputBijection rightCertificate).transfer
    (fun entry => entry.signalType.Denote) inputs

noncomputable def Corresponds.transferHierStep
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren)) :
    HierStep (ModuleStructure.composite rightBody rightChildren) :=
  { inputs := leftCertificate.transferInputs rightCertificate hierStep.inputs
    outputs := (leftCertificate.outputBijection rightCertificate).transfer
      (fun entry => entry.port.signalType.Denote) hierStep.outputs
    children := (leftCertificate.childBijection rightCertificate).transfer
      (fun entry => HierStep entry.module.moduleStructure) hierStep.children }

theorem Corresponds.transferInputs_agree (inputs : leftBody.ports.inputs.Values)
    (left : leftBody.ports.inputs.Label) (right : rightBody.ports.inputs.Label)
    (sameName : leftPorts.inputs.name left = rightPorts.inputs.name right) :
    HEq (inputs left) (leftCertificate.transferInputs rightCertificate inputs right) := by
  let bijection := leftCertificate.inputBijection rightCertificate
  have names := congrArg Port.name (bijection.preserves left)
  have equal : bijection.forward left = right :=
    enumeration_name_injective rightBody.ports.inputs.labels rightPorts.inputs.name
      rightCertificate.source_names_unique.1 (names.symm.trans sameName)
  subst right
  exact (bijection.transfer_forward (fun entry => entry.signalType.Denote) inputs left).symm

theorem Corresponds.transferChildOutputs_agree
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    (leftChild : leftBody.instancePorts.Name) (rightChild : rightBody.instancePorts.Name)
    (leftPort : (leftBody.instancePorts.ports leftChild).outputs.Label)
    (rightPort : (rightBody.instancePorts.ports rightChild).outputs.Label)
    (sameChild : leftName leftChild = rightName rightChild)
    (samePort : (leftNaming leftChild).ports.outputs.name leftPort =
      (rightNaming rightChild).ports.outputs.name rightPort) :
    HEq ((hierStep.children leftChild).outputs leftPort)
      (((leftCertificate.transferHierStep rightCertificate hierStep).children
        rightChild).outputs rightPort) := by
  let bijection := leftCertificate.childBijection rightCertificate
  have names := congrArg Child.name (bijection.preserves leftChild)
  have equal : bijection.forward leftChild = rightChild :=
    enumeration_name_injective rightBody.instancePorts.names rightName
      rightCertificate.source_names_unique.2.1 (names.symm.trans sameChild)
  subst rightChild
  exact namedModule_output_heq _ _ (congrArg Child.module (bijection.preserves leftChild))
    _ _ (bijection.transfer_forward
      (fun entry => HierStep entry.module.moduleStructure) hierStep.children leftChild).symm
    (leftCertificate.source_names_unique.2.2 leftChild) leftPort rightPort samePort

include leftCertificate in
theorem Corresponds.childInputsUnique (child : leftBody.instancePorts.Name) :
    (leftNaming child).ports.inputs.names.Nodup := by
  have unique := leftCertificate.unique
  rw [Option.some.inj leftCertificate.same] at unique
  have member := List.mem_map_of_mem (f := childEntry leftPorts leftName leftNaming)
    (leftBody.instancePorts.names.locate child).mem
  exact (List.nodup_append.mp (unique.2.2 _ member).1).1

theorem Corresponds.transferSourceValue (inputs : leftBody.ports.inputs.Values)
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    {leftType rightType : SignalType}
    (left : SignalSource leftBody.ports leftBody.instancePorts leftType)
    (right : SignalSource rightBody.ports rightBody.instancePorts rightType)
    (same : sourceDescription leftPorts leftName (fun child => (leftNaming child).ports) left =
      sourceDescription rightPorts rightName (fun child => (rightNaming child).ports) right) :
    HEq (left.value inputs hierStep.childOutputs)
      (right.value (leftCertificate.transferInputs rightCertificate inputs)
        (leftCertificate.transferHierStep rightCertificate hierStep).childOutputs) :=
  sourceDescription_value_heq leftPorts rightPorts leftName rightName
    (fun child => (leftNaming child).ports) (fun child => (rightNaming child).ports)
    inputs _ hierStep.childOutputs _
    (leftCertificate.transferInputs_agree rightCertificate inputs)
    (leftCertificate.transferChildOutputs_agree rightCertificate hierStep) left right same

theorem Corresponds.transferChildInputs (inputs : leftBody.ports.inputs.Values)
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    (child : leftBody.instancePorts.Name) :
    HEq (leftBody.wiring.childInputValues inputs hierStep.childOutputs child)
      (rightBody.wiring.childInputValues
        (leftCertificate.transferInputs rightCertificate inputs)
        (leftCertificate.transferHierStep rightCertificate hierStep).childOutputs
        ((leftCertificate.childBijection rightCertificate).forward child)) := by
  let bijection := leftCertificate.childBijection rightCertificate
  have childEqual := bijection.preserves child
  have moduleEqual := congrArg Child.module childEqual
  apply namedModule_inputs_heq _ _ moduleEqual
  intro leftPort rightPort sameName
  exact leftCertificate.transferSourceValue rightCertificate inputs hierStep
    (leftBody.wiring.instanceInput child leftPort)
    (rightBody.wiring.instanceInput (bijection.forward child) rightPort)
    (namedModule_input_source_eq _ _ moduleEqual _ _ (congrArg Child.inputs childEqual)
      (leftCertificate.childInputsUnique child) leftPort rightPort sameName)

theorem Corresponds.transferStoredChildInputs
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    (child : leftBody.instancePorts.Name) :
    HEq (hierStep.children child).inputs
      ((leftCertificate.transferHierStep rightCertificate hierStep).children
        ((leftCertificate.childBijection rightCertificate).forward child)).inputs := by
  let bijection := leftCertificate.childBijection rightCertificate
  exact namedModule_hierStep_inputs_heq _ _
    (congrArg Child.module (bijection.preserves child)) _ _
    (bijection.transfer_forward
      (fun entry => HierStep entry.module.moduleStructure)
      hierStep.children child).symm

/-- Generic structural soundness. Equal uniquely named descriptions preserve
the production solution relation under automatically derived boundary and
child correspondences. This includes every complete hierarchy assignment,
not just evaluation of a chosen example. -/
theorem Corresponds.transferSolution_iff
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren)) :
    (ModuleStructure.composite leftBody leftChildren).IsSolution hierStep ↔
      (ModuleStructure.composite rightBody rightChildren).IsSolution
        (leftCertificate.transferHierStep rightCertificate hierStep) := by
  let outputs := leftCertificate.outputBijection rightCertificate
  let children := leftCertificate.childBijection rightCertificate
  have boundary : HierStep.ParentOutputsSatisfy leftBody hierStep.inputs
      hierStep.outputs hierStep.childOutputs ↔
      HierStep.ParentOutputsSatisfy rightBody
        (leftCertificate.transferHierStep rightCertificate hierStep).inputs
        (leftCertificate.transferHierStep rightCertificate hierStep).outputs
        (leftCertificate.transferHierStep rightCertificate hierStep).childOutputs := by
    apply outputs.forall_iff
    intro port
    apply equality_iff_of_heq
    · exact (outputs.transfer_forward
        (fun entry => entry.port.signalType.Denote) hierStep.outputs port).symm
    · exact leftCertificate.transferSourceValue rightCertificate hierStep.inputs hierStep
        (leftBody.wiring.moduleOutput port) (rightBody.wiring.moduleOutput (outputs.forward port))
        (congrArg Connection.source (outputs.preserves port))
  have childInputs : HierStep.ChildInputsSatisfy leftBody hierStep.inputs
      hierStep.childInputs hierStep.childOutputs ↔
      HierStep.ChildInputsSatisfy rightBody
        (leftCertificate.transferHierStep rightCertificate hierStep).inputs
        (leftCertificate.transferHierStep rightCertificate hierStep).childInputs
        (leftCertificate.transferHierStep rightCertificate hierStep).childOutputs := by
    apply children.forall_iff
    intro child
    apply equality_iff_of_heq
    · exact leftCertificate.transferStoredChildInputs rightCertificate hierStep child
    · exact leftCertificate.transferChildInputs rightCertificate hierStep.inputs
        hierStep child
  have childSolutions : (∀ child, (leftChildren child).IsSolution
      (hierStep.children child)) ↔
      (∀ child, (rightChildren child).IsSolution
        ((leftCertificate.transferHierStep rightCertificate hierStep).children child)) := by
    apply children.forall_iff
    intro child
    exact namedModule_solution_iff _ _ (congrArg Child.module (children.preserves child))
      _ _ (children.transfer_forward
        (fun entry => HierStep entry.module.moduleStructure)
        hierStep.children child).symm
  exact and_congr boundary (and_congr childInputs childSolutions)

end Comparison


end Silean.Authoring.CircuitDescription
