import Silean.Authoring.CircuitDescription
import Silean.Semantics.StructuralEquations
import Silean.Contracts.Cycle.CycleImplementation

/-! Soundness of the circuit-description translation boundary. This file
reasons about production endpoints and structural equations; it does not define
another hardware interpreter. Endpoint matching uses canonical structural IDs;
emission names remain checked metadata but are not identity witnesses.

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

/-- Placing already-resolved sources never fails during connection
finalization, even when the draft-producing function contains pattern matches
or the child's port family has symbolic size. -/
@[circuit_description]
theorem Internal.finalizeConnections_map_of_sources {Index : Type}
    (indices : List Index) (draft : Index → DraftConnection)
    (source : Index → Source)
    (isSource : ∀ index, (draft index).driver.origin = .source (source index)) :
    Internal.finalizeConnections [] (indices.map draft) =
      .ok (indices.map fun index =>
        ({ port := (draft index).port, source := source index } : Connection)) := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      have driver : (draft head).driver =
          ({ origin := .source (source head) } : Net (draft head).port.signalType) := by
        cases driverEq : (draft head).driver with
        | mk origin =>
            have originEq := isSource head
            rw [driverEq] at originEq
            cases originEq
            rfl
      simp only [List.map_cons, Internal.finalizeConnections,
        Internal.finalizeConnection]
      rw [driver]
      simp only [Internal.resolveNet, ih]

/-- Canonical description-local IDs retain the identity of typed labels
without consulting emission names. -/
theorem portId_injective (signals : SignalMap) : Function.Injective (portId signals) := by
  intro left right same
  apply signals.labels.ordinal_injective
  apply Fin.ext
  exact congrArg PortId.index same

theorem childId_injective (instances : InstancePorts) : Function.Injective (childId instances) := by
  intro left right same
  apply instances.names.ordinal_injective
  apply Fin.ext
  exact congrArg ChildId.index same

/-- Include the signal type when comparing endpoints so equality also
transports the dependent source type. -/
def packedSourceDescription {body : ModuleBody}
    (source : (signalType : SignalType) × SignalSource body.ports body.instancePorts signalType) :
    Source := sourceDescription source.2

theorem packedSourceDescription_injective {body : ModuleBody}
    {left right : (signalType : SignalType) ×
      SignalSource body.ports body.instancePorts signalType}
    (same : packedSourceDescription left = packedSourceDescription right) : left = right := by
  rcases left with ⟨_, left⟩
  rcases right with ⟨_, right⟩
  cases left with
  | moduleInput left =>
    cases right with
    | moduleInput right =>
      have equal := portId_injective body.ports.inputs (Source.input.inj same)
      cases equal
      rfl
    | instanceOutput child port => cases same
  | instanceOutput leftChild leftPort =>
    cases right with
    | moduleInput right => cases same
    | instanceOutput rightChild rightPort =>
      have ids := Source.child.inj same
      have equal := childId_injective body.instancePorts ids.1
      cases equal
      have portEqual := portId_injective
        (body.instancePorts.ports leftChild).outputs ids.2
      cases portEqual
      rfl

/-- Equal structural driver IDs of a fixed type are equal production drivers. -/
theorem sourceDescription_injective {body : ModuleBody}
    {left right : SignalSource body.ports body.instancePorts signalType}
    (same : sourceDescription left = sourceDescription right) : left = right := by
  have packed := packedSourceDescription_injective
    (left := ⟨signalType, left⟩) (right := ⟨signalType, right⟩) same
  exact eq_of_heq (Sigma.mk.inj packed).2

/-- This uses the production source evaluator; structural IDs introduce no
alternate hardware interpretation. -/
theorem sourceDescription_value_eq {body : ModuleBody}
    {left right : SignalSource body.ports body.instancePorts signalType}
    (same : sourceDescription left = sourceDescription right)
    (inputs : body.ports.inputs.Values)
    (childOutputs : (child : body.instancePorts.Name) →
      (body.instancePorts.ports child).outputs.Values) :
    left.value inputs childOutputs = right.value inputs childOutputs := by
  rw [sourceDescription_injective same]


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

/-- Equal ordered entry lists give a bijection even when their label types
differ. Canonical structural IDs make the entry functions injective without
any assumption about emitted names. -/
noncomputable def matchingEntries {α : Type u} {β : Type v} {γ : Type w}
    (leftLabels : Enumeration α) (rightLabels : Enumeration β)
    (left : α → γ) (right : β → γ)
    (same : leftLabels.values.map left = rightLabels.values.map right)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right) :
    EntryBijection left right := by
  classical
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
    (label : signals.Label) : Port :=
  ⟨portId signals label, names.name label, signals.signalType label⟩

abbrev outputEntry {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (label : body.ports.outputs.Label) : Connection :=
  ⟨inputEntry body.ports.outputs ports.outputs label,
    sourceDescription (body.wiring.moduleOutput label)⟩

abbrev childEntry {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) → ModuleNaming (children child))
    (child : body.instancePorts.Name) : Child :=
  { id := childId body.instancePorts child
    name := instanceName child
    module := ⟨body.instancePorts.ports child, children child, childNaming child⟩
    inputs := (body.instancePorts.ports child).inputs.labels.values.map fun port =>
      ⟨inputEntry (body.instancePorts.ports child).inputs (childNaming child).ports.inputs port,
        sourceDescription (body.wiring.instanceInput child port)⟩ }

/-- Equal actual children and corresponding hierarchy assignments have corresponding
output values. This inspects neither the child implementation nor its proof. -/
theorem namedModule_output_heq (left right : NamedModule) (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (stepsEqual : HEq leftStep rightStep)
    (leftPort : left.ports.outputs.Label) (rightPort : right.ports.outputs.Label)
    (idsEqual : portId left.ports.outputs leftPort =
      portId right.ports.outputs rightPort) :
    HEq (leftStep.outputs leftPort) (rightStep.outputs rightPort) := by
  cases same
  have equal := eq_of_heq stepsEqual
  cases equal
  have portEqual := portId_injective left.ports.outputs idsEqual
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
    (leftPort : left.ports.inputs.Label) (rightPort : right.ports.inputs.Label)
    (sameId : portId left.ports.inputs leftPort = portId right.ports.inputs rightPort) :
    leftSource leftPort = rightSource rightPort := by
  cases same
  have equal := portId_injective left.ports.inputs sameId
  cases equal
  exact congrArg Connection.source ((List.map_inj_left.mp sameInputs)
    leftPort (left.ports.inputs.labels.locate leftPort).mem)

theorem namedModule_inputs_heq (left right : NamedModule) (same : left = right)
    (leftInputs : left.ports.inputs.Values) (rightInputs : right.ports.inputs.Values)
    (agree : ∀ leftPort rightPort,
      portId left.ports.inputs leftPort = portId right.ports.inputs rightPort →
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

theorem namedModule_currentState_heq (left right : NamedModule)
    (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (sameStep : HEq leftStep rightStep) :
    HEq (HierStep.currentState left.moduleStructure leftStep)
      (HierStep.currentState right.moduleStructure rightStep) := by
  cases same
  cases eq_of_heq sameStep
  rfl

theorem namedModule_nextState_heq (left right : NamedModule)
    (same : left = right)
    (leftStep : HierStep left.moduleStructure)
    (rightStep : HierStep right.moduleStructure)
    (sameStep : HEq leftStep rightStep) :
    HEq (HierStep.nextState left.moduleStructure leftStep)
      (HierStep.nextState right.moduleStructure rightStep) := by
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

/-- Structurally aligned production valuations give the same value to
corresponding sources, even across different boundary and instance-label types. The
bijections above are what will supply the alignment, rather than an author
assumption or a second interpreter. -/
theorem sourceDescription_value_heq
    {leftBody rightBody : ModuleBody}
    (leftInputs : leftBody.ports.inputs.Values)
    (rightInputs : rightBody.ports.inputs.Values)
    (leftOutputs : (child : leftBody.instancePorts.Name) →
      (leftBody.instancePorts.ports child).outputs.Values)
    (rightOutputs : (child : rightBody.instancePorts.Name) →
      (rightBody.instancePorts.ports child).outputs.Values)
    (inputsAgree : ∀ left right,
      portId leftBody.ports.inputs left = portId rightBody.ports.inputs right →
      HEq (leftInputs left) (rightInputs right))
    (outputsAgree : ∀ leftChild rightChild leftPort rightPort,
      childId leftBody.instancePorts leftChild = childId rightBody.instancePorts rightChild →
      portId (leftBody.instancePorts.ports leftChild).outputs leftPort =
        portId (rightBody.instancePorts.ports rightChild).outputs rightPort →
      HEq (leftOutputs leftChild leftPort) (rightOutputs rightChild rightPort))
    {leftType rightType : SignalType}
    (left : SignalSource leftBody.ports leftBody.instancePorts leftType)
    (right : SignalSource rightBody.ports rightBody.instancePorts rightType)
    (same : sourceDescription left = sourceDescription right) :
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
  {leftNamedWires : List (Naming.NamedWire leftBody)}
  {rightNamedWires : List (Naming.NamedWire rightBody)}
  (leftCertificate : Corresponds description
    (ModuleNaming.composite leftKey leftPorts leftName leftNaming leftNamedWires))
  (rightCertificate : Corresponds description
    (ModuleNaming.composite rightKey rightPorts rightName rightNaming rightNamedWires))

/-- Complete parent-input correspondence preserves structural IDs, metadata,
and signal types even when label types differ. -/
noncomputable def Corresponds.inputBijection :
    EntryBijection (inputEntry leftBody.ports.inputs leftPorts.inputs)
      (inputEntry rightBody.ports.inputs rightPorts.inputs) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.ports.inputs.labels rightBody.ports.inputs.labels
    _ _ (congrArg Description.inputs descriptions)
  · intro left right same
    exact portId_injective leftBody.ports.inputs (congrArg Port.id same)
  · intro left right same
    exact portId_injective rightBody.ports.inputs (congrArg Port.id same)

/-- Parent-output correspondence preserves the complete sink entry, including
its structural ID, driven source, emission name, and signal type. -/
noncomputable def Corresponds.outputBijection :
    EntryBijection (outputEntry leftPorts) (outputEntry rightPorts) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.ports.outputs.labels rightBody.ports.outputs.labels
    _ _ (congrArg Description.outputs descriptions)
  · intro left right same
    exact portId_injective leftBody.ports.outputs (congrArg (fun entry => entry.port.id) same)
  · intro left right same
    exact portId_injective rightBody.ports.outputs (congrArg (fun entry => entry.port.id) same)

/-- Child correspondence preserves the structural child ID, full `NamedModule`,
emission name, and every input connection. -/
noncomputable def Corresponds.childBijection :
    EntryBijection (childEntry leftName leftNaming)
      (childEntry rightName rightNaming) := by
  have descriptions := Option.some.inj (leftCertificate.same.symm.trans rightCertificate.same)
  apply matchingEntries leftBody.instancePorts.names rightBody.instancePorts.names
    _ _ (congrArg Description.children descriptions)
  · intro left right same
    exact childId_injective leftBody.instancePorts (congrArg Child.id same)
  · intro left right same
    exact childId_injective rightBody.instancePorts (congrArg Child.id same)

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

theorem Corresponds.transferCurrentState
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren)) :
    (leftCertificate.childBijection rightCertificate).transfer
        (fun entry => entry.module.moduleStructure.State) hierStep.currentState =
      (leftCertificate.transferHierStep rightCertificate hierStep).currentState := by
  funext rightChild
  let bijection := leftCertificate.childBijection rightCertificate
  let leftChild := bijection.backward rightChild
  have modules := congrArg Child.module (bijection.backward_preserves rightChild)
  have stepTransfer : HEq
      ((leftCertificate.transferHierStep rightCertificate hierStep).children rightChild)
      (hierStep.children leftChild) :=
    cast_heq _ _
  have stateTransfer : HEq
      (bijection.transfer (fun entry => entry.module.moduleStructure.State)
        hierStep.currentState rightChild)
      (HierStep.currentState (leftChildren leftChild)
        (hierStep.children leftChild)) :=
    cast_heq _ _
  exact eq_of_heq (stateTransfer.trans <|
    namedModule_currentState_heq _ _ modules
      (hierStep.children leftChild)
      ((leftCertificate.transferHierStep rightCertificate hierStep).children rightChild)
      stepTransfer.symm)

theorem Corresponds.transferNextState
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren)) :
    (leftCertificate.childBijection rightCertificate).transfer
        (fun entry => entry.module.moduleStructure.State) hierStep.nextState =
      (leftCertificate.transferHierStep rightCertificate hierStep).nextState := by
  funext rightChild
  let bijection := leftCertificate.childBijection rightCertificate
  let leftChild := bijection.backward rightChild
  have modules := congrArg Child.module (bijection.backward_preserves rightChild)
  have stepTransfer : HEq
      ((leftCertificate.transferHierStep rightCertificate hierStep).children rightChild)
      (hierStep.children leftChild) :=
    cast_heq _ _
  have stateTransfer : HEq
      (bijection.transfer (fun entry => entry.module.moduleStructure.State)
        hierStep.nextState rightChild)
      (HierStep.nextState (leftChildren leftChild)
        (hierStep.children leftChild)) :=
    cast_heq _ _
  exact eq_of_heq (stateTransfer.trans <|
    namedModule_nextState_heq _ _ modules
      (hierStep.children leftChild)
      ((leftCertificate.transferHierStep rightCertificate hierStep).children rightChild)
      stepTransfer.symm)

theorem Corresponds.transferInputs_agree (inputs : leftBody.ports.inputs.Values)
    (left : leftBody.ports.inputs.Label) (right : rightBody.ports.inputs.Label)
    (sameId : portId leftBody.ports.inputs left = portId rightBody.ports.inputs right) :
    HEq (inputs left) (leftCertificate.transferInputs rightCertificate inputs right) := by
  let bijection := leftCertificate.inputBijection rightCertificate
  have ids := congrArg Port.id (bijection.preserves left)
  have equal : bijection.forward left = right :=
    portId_injective rightBody.ports.inputs (ids.symm.trans sameId)
  subst right
  exact (bijection.transfer_forward (fun entry => entry.signalType.Denote) inputs left).symm

theorem Corresponds.transferOutputs_agree
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    (left : leftBody.ports.outputs.Label) (right : rightBody.ports.outputs.Label)
    (sameId : portId leftBody.ports.outputs left = portId rightBody.ports.outputs right) :
    HEq (hierStep.outputs left)
      ((leftCertificate.transferHierStep rightCertificate hierStep).outputs right) := by
  let bijection := leftCertificate.outputBijection rightCertificate
  have ids := congrArg (fun entry => entry.port.id) (bijection.preserves left)
  have equal : bijection.forward left = right :=
    portId_injective rightBody.ports.outputs (ids.symm.trans sameId)
  subst right
  exact (bijection.transfer_forward
    (fun entry => entry.port.signalType.Denote) hierStep.outputs left).symm

theorem Corresponds.transferChildOutputs_agree
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    (leftChild : leftBody.instancePorts.Name) (rightChild : rightBody.instancePorts.Name)
    (leftPort : (leftBody.instancePorts.ports leftChild).outputs.Label)
    (rightPort : (rightBody.instancePorts.ports rightChild).outputs.Label)
    (sameChild : childId leftBody.instancePorts leftChild =
      childId rightBody.instancePorts rightChild)
    (samePort : portId (leftBody.instancePorts.ports leftChild).outputs leftPort =
      portId (rightBody.instancePorts.ports rightChild).outputs rightPort) :
    HEq ((hierStep.children leftChild).outputs leftPort)
      (((leftCertificate.transferHierStep rightCertificate hierStep).children
        rightChild).outputs rightPort) := by
  let bijection := leftCertificate.childBijection rightCertificate
  have ids := congrArg Child.id (bijection.preserves leftChild)
  have equal : bijection.forward leftChild = rightChild :=
    childId_injective rightBody.instancePorts (ids.symm.trans sameChild)
  subst rightChild
  exact namedModule_output_heq _ _ (congrArg Child.module (bijection.preserves leftChild))
    _ _ (bijection.transfer_forward
      (fun entry => HierStep entry.module.moduleStructure) hierStep.children leftChild).symm
    leftPort rightPort samePort

theorem Corresponds.transferSourceValue (inputs : leftBody.ports.inputs.Values)
    (hierStep : HierStep (ModuleStructure.composite leftBody leftChildren))
    {leftType rightType : SignalType}
    (left : SignalSource leftBody.ports leftBody.instancePorts leftType)
    (right : SignalSource rightBody.ports rightBody.instancePorts rightType)
    (same : sourceDescription left = sourceDescription right) :
    HEq (left.value inputs hierStep.childOutputs)
      (right.value (leftCertificate.transferInputs rightCertificate inputs)
        (leftCertificate.transferHierStep rightCertificate hierStep).childOutputs) :=
  sourceDescription_value_heq inputs _ hierStep.childOutputs _
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
  intro leftPort rightPort sameId
  exact leftCertificate.transferSourceValue rightCertificate inputs hierStep
    (leftBody.wiring.instanceInput child leftPort)
    (rightBody.wiring.instanceInput (bijection.forward child) rightPort)
    (namedModule_input_source_eq _ _ moduleEqual _ _ (congrArg Child.inputs childEqual)
      leftPort rightPort sameId)

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

/-- Generic structural soundness. Equal descriptions preserve the production
solution relation under automatically derived structural-ID correspondences;
no emitted-name uniqueness assumption is required. This includes every
complete hierarchy assignment, not just evaluation of a chosen example. -/
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
