import Silean.Modules.All.All
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Eq
import Silean.Composition.SignalLogic
import Silean.Authoring.CircuitDescription

namespace Silean.Modules.Equality

open Silean
open Contracts.Cycle.Certification.Layer

/-! # Structural equality

Aggregate values are compared recursively and the component results are
reduced with AND. Ordinary Lean recursion is the clearest description of this
type-directed hierarchy, so it remains in this file rather than being expanded
through fixed-module authoring syntax. Recursive certification is kept in
`Internal/EqualityVerification.lean`; public structural guarantees are in
`EqualityTheorems.lean`. -/

/-! ## Interface and exact behavior -/

inductive Input | left | right
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun | .left | .right => signalType

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .result => .bit

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap⟩

inductive Rule | apply
deriving Enumeration

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) emptySignalMap where
  readsInputs := .all (inputMap signalType)
  writesOutputs := .all outputMap
  target inputs _ := fun
    | .result => signalType.equal (inputs .left) (inputs .right)

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule signalType
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .result = signalType.equal (inputs .left) (inputs .right) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

theorem output_eq_true_iff_of_holds (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values)
    (holds : (outputRule signalType).Holds inputs state outputs) :
    outputs .result = true ↔ inputs .left = inputs .right := by
  rw [(outputRule_holds_iff signalType inputs state outputs).mp holds]
  exact signalType.equal_eq_true_iff _ _

/-! ## Hardware structure

The bit case is a transparent wrapper around the closed equality
primitive. -/

inductive BitInstance
  /-- The one-bit equality primitive. -/
  | gate
deriving Enumeration

@[reducible] def bitInstances : InstancePorts :=
  EnumeratedMap.of BitInstance fun | .gate => Primitives.eq.ports

@[reducible] def bitContext : EndpointContext where
  ports := ports .bit
  instancePorts := bitInstances

def bitWiring : Wiring bitContext.ports bitContext.instancePorts where
  -- The primitive result is the module result.
  moduleOutput | .result => bitContext.instanceOutput .gate .output
  -- Both operands feed the equality primitive.
  instanceInput
    | .gate, .left => bitContext.moduleInput .left
    | .gate, .right => bitContext.moduleInput .right

@[reducible] def bitBody : ModuleBody := ⟨bitContext, bitWiring⟩


@[reducible] def bitStructuralChildren :
    (child : bitInstances.Name) → ModuleStructure (bitInstances.ports child)
  | .gate => .primitive Primitives.eq

def bitModuleStructure : ModuleStructure (ports .bit) :=
  .composite bitBody bitStructuralChildren


/-! Aggregate equality has two operand splitters, one recursive equality
instance per
immediate component, and one `All` child consuming the family of results. -/

abbrev AggregateInstance (splitter : Composition.SignalSplitter) :=
  Sum Input (Sum splitter.ports.outputs.Label PUnit)

@[reducible] def aggregateInstanceEnumeration (splitter : Composition.SignalSplitter) :
    Enumeration (AggregateInstance splitter) :=
  Enumeration.sum inferInstance
    (Enumeration.sum splitter.ports.outputs.labels Enumeration.punit)

namespace Internal

abbrev splitInstance (input : Input) : AggregateInstance splitter := .inl input
abbrev componentInstance (component : splitter.ports.outputs.Label) :
    AggregateInstance splitter := .inr (.inl component)
abbrev allInstance : AggregateInstance splitter := .inr (.inr .unit)

end Internal

def componentCount (splitter : Composition.SignalSplitter) : Nat :=
  splitter.ports.outputs.labels.values.length

@[reducible] def aggregateInstances (splitter : Composition.SignalSplitter) : InstancePorts where
  Key := AggregateInstance splitter
  keys := aggregateInstanceEnumeration splitter
  value
    | .inl _ => splitter.ports
    | .inr (.inl component) =>
        ports (splitter.ports.outputs.signalType component)
    | .inr (.inr _) => All.ports (componentCount splitter)

@[reducible] def aggregateContext (splitter : Composition.SignalSplitter) : EndpointContext where
  ports := ports splitter.aggregateType
  instancePorts := aggregateInstances splitter

namespace Internal

def componentAt (splitter : Composition.SignalSplitter)
    (index : Fin (componentCount splitter)) : splitter.ports.outputs.Label :=
  splitter.ports.outputs.labels.values[index.val]'(by
    simp [componentCount])

@[simp] theorem componentAt_ordinal (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) :
    componentAt splitter (splitter.ports.outputs.labels.ordinal component) =
      component := by
  exact (splitter.ports.outputs.labels.locate component).get_eq

end Internal

def aggregateWiring (splitter : Composition.SignalSplitter) :
    Wiring (aggregateContext splitter).ports (aggregateContext splitter).instancePorts where
  moduleOutput
    -- The reduction result is the aggregate equality result.
    | .result =>
        (aggregateContext splitter).instanceOutput Internal.allInstance .output
  instanceInput
    -- Split the left and right operands into matching components.
    | .inl input, aggregateInput => by
        cases splitter with
        | vector length element =>
            cases aggregateInput
            cases input with
            | left => exact (aggregateContext (.vector length element)).moduleInput .left
            | right => exact (aggregateContext (.vector length element)).moduleInput .right
        | tuple fields =>
            cases aggregateInput
            cases input with
            | left => exact (aggregateContext (.tuple fields)).moduleInput .left
            | right => exact (aggregateContext (.tuple fields)).moduleInput .right
    | .inr (.inl component), .left =>
        (aggregateContext splitter).instanceOutput
          (Internal.splitInstance .left) component
    | .inr (.inl component), .right =>
        (aggregateContext splitter).instanceOutput
          (Internal.splitInstance .right) component
    -- Feed every component comparison into the `All` reduction.
    | .inr (.inr _), input =>
        (aggregateContext splitter).instanceOutput
          (Internal.componentInstance (Internal.componentAt splitter
            (All.inputIndex (componentCount splitter) input))) .result

@[reducible] def aggregateBody (splitter : Composition.SignalSplitter) : ModuleBody :=
  ⟨aggregateContext splitter, aggregateWiring splitter⟩

def moduleStructure : (signalType : SignalType) → ModuleStructure (ports signalType)
  | .bit => bitModuleStructure
  | .vector length elementType =>
      .composite (aggregateBody (.vector length elementType)) fun
        | .inl _ => .splitter (.vector length elementType)
        | .inr (.inl _) => moduleStructure elementType
        | .inr (.inr _) =>
            All.moduleStructure (componentCount (.vector length elementType))
  | .tuple fields =>
      .composite (aggregateBody (.tuple fields)) fun
        | .inl _ => .splitter (.tuple fields)
        | .inr (.inl component) => moduleStructure (fields.typeAt component)
        | .inr (.inr _) =>
            All.moduleStructure (componentCount (.tuple fields))
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller


/-- Contract-facing equality result law over the shared boundary-step API. -/
theorem result_of_allowed (signalType : SignalType)
    {step : (cycleContract signalType).Step}
    (allowed : (cycleContract signalType).Allows step) :
    step.outputs .result =
      signalType.equal (step.inputs .left) (step.inputs .right) :=
  (outputRule_holds_iff signalType step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end Silean.Modules.Equality

namespace Silean.Modules.Equality.Naming

open Silean Silean.Naming

private def indexedComponent (signals : SignalMap) (component : signals.Label) :
    SourceName :=
  .scoped "equal" ((SignalMapNaming.indexed signals "component").name component)

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Equality.ports signalType) where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .left | .right => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Equality.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith : (signalType : SignalType) → SignalTypeNaming signalType →
    ModuleNaming (Modules.Equality.moduleStructure signalType)
  | .bit, _ => by
      rw [Modules.Equality.moduleStructure]
      unfold Modules.Equality.bitModuleStructure
      exact .composite ⟨"equality", "bit", []⟩ (ports .bit)
        (fun | .gate => "gate") (fun | .gate => Silean.Naming.Primitive.eq)
  | .vector length elementType, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : Composition.SignalSplitter := .vector length elementType
      exact .composite ⟨"equality", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => .scoped "equal" (.indexed "component" component.val)
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inr (.inl component) =>
              namingWith elementType (typeNaming.component component)
          | .inr (.inr _) => All.Naming.naming (Modules.Equality.componentCount splitter))
  | .tuple fields, typeNaming => by
      rw [Modules.Equality.moduleStructure]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"equality", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .inl .left => "split_left"
          | .inl .right => "split_right"
          | .inr (.inl component) => indexedComponent splitter.ports.outputs component
          | .inr (.inr _) => "all")
        (fun
          | .inl .left =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inl .right =>
              Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .inr (.inl component) =>
              namingWith (fields.typeAt component) (typeNaming.component component)
          | .inr (.inr _) => All.Naming.naming (Modules.Equality.componentCount splitter))
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Equality.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

/-- Recursive equality implementation details do not change its declared
boundary naming. -/
theorem naming_ports (signalType : SignalType) :
    (naming signalType).ports = ports signalType := by
  unfold naming
  cases signalType with
  | bit =>
      rw [namingWith.eq_1]
      erw [ModuleNaming.ports_mpr_of_eq Modules.Equality.moduleStructure.eq_1]
      rfl
  | vector length element =>
      rw [namingWith.eq_2]
      erw [ModuleNaming.ports_mpr_of_eq
        (Modules.Equality.moduleStructure.eq_2 length element)]
      rfl
  | tuple fields =>
      rw [namingWith.eq_3]
      erw [ModuleNaming.ports_mpr_of_eq
        (Modules.Equality.moduleStructure.eq_3 fields)]
      rfl

/-- The emitted boundary names of structural equality are collision-free. -/
theorem portNames_nodup (signalType : SignalType) :
    (naming signalType).ports.names.Nodup := by
  rw [naming_ports]
  exact of_decide_eq_true rfl

end Silean.Modules.Equality.Naming

namespace Silean.Modules.Equality

@[reducible] def design (signalType : SignalType) : Silean.Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType
  naming := Naming.naming signalType

/-! ## Placement -/

open Silean.Authoring.CircuitDescription

/-- Place structural equality under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (left right : Net signalType) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType) fun
      | .left => left
      | .right => right
  pure (child .result)

/-- Place structural equality using the next conventional indexed name. -/
noncomputable def place (left right : Net signalType) : Builder (Net .bit) := do
  let child ← placeIndexed "equality" (design signalType) fun
    | .left => left
    | .right => right
  pure (child .result)

attribute [circuit_description] placeNamed place

end Silean.Modules.Equality
