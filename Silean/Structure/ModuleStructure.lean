import Silean.Structure.Primitive
import Silean.Composition.SignalAdapter
import Silean.Structure.ModuleBody

namespace Silean

/-! # Hardware hierarchy

`ModuleStructure` is the complete structural description consumed by
structural semantics, naming, and FIRRTL generation. It contains no behavioral
contract and no evaluation schedule.

A composite gives one level of typed wiring and assigns a structure to every
named instance. Reusing the same child definition at several names creates
several hardware instances. Primitive and signal-adapter leaves terminate the
hierarchy.

The wiring denotes simultaneous equations rather than an execution order.
`StructuralEquations` defines what it means for proposed wire values to solve
those equations; separate existence and uniqueness proofs establish that the
structure has one well-defined result. -/

inductive ModuleStructure : ModulePorts → Type 1
  /-- A leaf implemented by a primitive. -/
  | primitive (primitive : Primitive) : ModuleStructure primitive.ports
  /-- An opaque leaf whose equations give assumed boundary behavior. This is
  used to compose and verify a parent before the child's structure exists. -/
  | blackbox (behavior : Primitive) : ModuleStructure behavior.ports
  /-- A leaf that separates an aggregate signal into its components. -/
  | splitter (splitter : Composition.SignalSplitter) : ModuleStructure splitter.ports
  /-- A leaf that joins component signals into an aggregate signal. -/
  | combiner (combiner : Composition.SignalCombiner) : ModuleStructure combiner.ports
  /-- One level of child interfaces and wiring, together with a structural
  implementation for every child instance. -/
  | composite (body : ModuleBody)
      (childStructure : (name : body.instancePorts.Name) →
        ModuleStructure (body.instancePorts.ports name)) :
      ModuleStructure body.ports

/-! Structural state is obtained from the complete module definition. A
composite branch is labelled by its instance names and recursively contains
the state of the actual child module attached at each name. -/

def ModuleStructure.structuralState (module : ModuleStructure ports) : StructuralState :=
  match module with
  | .primitive gate => .leaf gate.localState
  | .blackbox behavior => .leaf behavior.localState
  | .splitter _ => .leaf emptySignalMap
  | .combiner _ => .leaf emptySignalMap
  | .composite body childStructure =>
      .children
        { Key := body.instancePorts.Name
          keys := body.instancePorts.names
          value := fun name => (childStructure name).structuralState }

namespace ModuleStructure

/-! Blackboxes are useful while composing an incomplete design and for
intentional external IP. `HasNoBlackboxes` is the stronger, recursive claim
that every leaf in a complete hierarchy has a concrete Silean structure. -/

def HasNoBlackboxes : ModuleStructure ports → Prop
  | .primitive _ => True
  | .blackbox _ => False
  | .splitter _ => True
  | .combiner _ => True
  | .composite _ children => ∀ name, (children name).HasNoBlackboxes

def hasNoBlackboxes : ModuleStructure ports → Bool
  | .primitive _ => true
  | .blackbox _ => false
  | .splitter _ => true
  | .combiner _ => true
  | .composite body children =>
      body.instancePorts.names.values.all fun name =>
        (children name).hasNoBlackboxes

@[simp] theorem hasNoBlackboxes_eq_true_iff
    (module : ModuleStructure ports) :
    module.hasNoBlackboxes = true ↔ module.HasNoBlackboxes := by
  induction module with
  | primitive | blackbox | splitter | combiner =>
      simp [hasNoBlackboxes, HasNoBlackboxes]
  | @composite body children induction =>
      rw [hasNoBlackboxes, HasNoBlackboxes, List.all_eq_true]
      constructor
      · intro every name
        apply (induction name).mp
        exact every name (ListIndex.get_eq
          (body.instancePorts.names.locate name) ▸ List.get_mem _ _)
      · intro every name member
        exact (induction name).mpr (every name)

instance instDecidableHasNoBlackboxes (module : ModuleStructure ports) :
    Decidable module.HasNoBlackboxes :=
  decidable_of_iff (module.hasNoBlackboxes = true)
    module.hasNoBlackboxes_eq_true_iff

@[simp] theorem hasNoBlackboxes_primitive (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasNoBlackboxes :=
  trivial

@[simp] theorem not_hasNoBlackboxes_blackbox (behavior : Primitive) :
    ¬(ModuleStructure.blackbox behavior).HasNoBlackboxes :=
  id

@[simp] theorem hasNoBlackboxes_splitter
    (splitter : Composition.SignalSplitter) :
    (ModuleStructure.splitter splitter).HasNoBlackboxes :=
  trivial

@[simp] theorem hasNoBlackboxes_combiner
    (combiner : Composition.SignalCombiner) :
    (ModuleStructure.combiner combiner).HasNoBlackboxes :=
  trivial

@[simp] theorem hasNoBlackboxes_composite_iff
    (body : ModuleBody)
    (children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)) :
    (ModuleStructure.composite body children).HasNoBlackboxes ↔
      ∀ name, (children name).HasNoBlackboxes :=
  Iff.rfl

theorem HasNoBlackboxes.child
    {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (closed : (ModuleStructure.composite body children).HasNoBlackboxes)
    (name : body.instancePorts.Name) :
    (children name).HasNoBlackboxes :=
  closed name

theorem HasNoBlackboxes.composite
    {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (childrenClosed : ∀ name, (children name).HasNoBlackboxes) :
    (ModuleStructure.composite body children).HasNoBlackboxes :=
  childrenClosed

/-- Reusable evidence that the executable hierarchy check succeeded. This is
indexed by an existing structure: it does not wrap or duplicate that
structure. -/
structure NoBlackboxesCertified (module : ModuleStructure ports) : Prop where
  checked : module.hasNoBlackboxes = true

namespace NoBlackboxesCertified

/-- A checked certificate implies the logical recursive closure property. -/
theorem hasNoBlackboxes (certified : NoBlackboxesCertified module) :
    module.HasNoBlackboxes :=
  module.hasNoBlackboxes_eq_true_iff.mp certified.checked

theorem primitive (primitive : Primitive) :
    NoBlackboxesCertified (.primitive primitive) :=
  ⟨rfl⟩

theorem splitter (splitter : Composition.SignalSplitter) :
    NoBlackboxesCertified (.splitter splitter) :=
  ⟨rfl⟩

theorem combiner (combiner : Composition.SignalCombiner) :
    NoBlackboxesCertified (.combiner combiner) :=
  ⟨rfl⟩

/-- Construct a composite certificate from certificates for all of its
children. -/
theorem composite
    {body : ModuleBody}
    {children : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name)}
    (childrenCertified : ∀ name, NoBlackboxesCertified (children name)) :
    NoBlackboxesCertified (.composite body children) := by
  constructor
  apply (ModuleStructure.hasNoBlackboxes_eq_true_iff _).mpr
  intro name
  exact (childrenCertified name).hasNoBlackboxes

end NoBlackboxesCertified

end ModuleStructure

end Silean
