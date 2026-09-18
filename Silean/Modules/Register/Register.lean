import Silean.Composition.LeafwiseComposition
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Register
import Silean.Authoring.CircuitDescription

namespace Silean.Modules.Register

open Silean

/-! # Generic register

A register for any signal type. Aggregate registers are recursively built from
registers for their component signal types.

`Register` is the generic recursive leaf mechanism used to construct all
stateful aggregate storage: bits use the primitive register, while vectors and
tuples are split, registered componentwise, and recombined. A separate builder
description would merely duplicate this recursion and hide the important
type-directed construction, so the recursive structure itself remains here as
the human-facing hardware definition.

The public behavioral and certification results are in
`RegisterTheorems.lean`; their recursive proof machinery is under
`Internal/`.
-/

/-! ## Boundary and cycle contract -/

@[reducible] def interface : Composition.LeafwiseInterface where
  Input := Primitives.UnaryInput
  inputs := inferInstance
  RecursiveInput := PUnit
  recursiveInputs := Enumeration.punit
  FixedInput := NoSignal
  fixedInputs := inferInstance
  inputLayout := {
    classify := fun | .input => .inl .unit
    label := fun | .inl _ => .input | .inr impossible => nomatch impossible
    classify_label := by intro part; cases part with
      | inl value => cases value; rfl
      | inr impossible => exact nomatch impossible
    label_classify := by intro inputName; cases inputName; rfl }
  fixedInputType := fun impossible => nomatch impossible
  Output := Primitives.SingleOutput
  outputs := inferInstance
  State := Primitives.RegisterState
  states := inferInstance

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  interface.inputMap signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  interface.outputMap signalType

@[reducible] def stateMap (signalType : SignalType) : SignalMap :=
  interface.stateMap signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  interface.ports signalType

abbrev Rule := Primitives.RegisterRule

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType) where
  readsInputs := .empty (inputMap signalType)
  writesOutputs := .all (outputMap signalType)
  target _ state := fun | .output => state .stored

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (ports signalType) (stateMap signalType) where
  readsInputs := .all (inputMap signalType)
  target inputs _ := fun | .stored => inputs .input

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => outputRule signalType
  stateRule := stateRule signalType
  outputCoverage := by rfl

/-! ## Hardware structure

A bit is one register primitive. A vector or tuple is split into its immediate
components, registered recursively, and recombined with the same shape. -/

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  interface.moduleStructure (.primitive Primitives.register) signalType

end Silean.Modules.Register

namespace Silean.Modules.Register.Naming

open Silean Silean.Naming

/-! ## Emission naming -/

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Register.ports signalType) where
  inputs := ⟨fun | .input => "in"⟩
  outputs := ⟨fun | .output => "out"⟩
  inputTypes := fun | .input => typeNaming
  outputTypes := fun | .output => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.Register.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

private def componentName (splitter : Composition.SignalSplitter)
    (component : splitter.ports.outputs.Label) : SourceName :=
  .scoped "register"
    ((SignalMapNaming.indexed splitter.ports.outputs "component").name component)

private def namingForType : (signalType : SignalType) → SignalTypeNaming signalType →
      ModuleNaming (Modules.Register.moduleStructure signalType)
  | .bit, _ => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_1]
      exact Silean.Naming.Primitive.register
  | .vector length elementType, typeNaming => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_2]
      let splitter : Composition.SignalSplitter := .vector length elementType
      exact .composite ⟨"register", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => .scoped "register" (.indexed "component" component.val)
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component =>
              namingForType elementType (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
  | .tuple fields, typeNaming => by
      unfold Modules.Register.moduleStructure
      rw [Composition.LeafwiseInterface.moduleStructure.eq_3]
      let splitter : Composition.SignalSplitter := .tuple fields
      exact .composite ⟨"register", "structural", [.signalType splitter.aggregateType]⟩
        (portsWithNaming splitter.aggregateType typeNaming)
        (fun
          | .splitter .unit => "split"
          | .component component => componentName splitter component
          | .combiner .output => "combine")
        (fun
          | .splitter .unit => Silean.Naming.SignalAdapter.splitterWithNaming splitter typeNaming
          | .component component => by
              exact namingForType (fields.typeAt component)
                (typeNaming.component component)
          | .combiner .output => Silean.Naming.SignalAdapter.combinerWithNaming splitter.combiner typeNaming)
termination_by signalType => signalType.complexity
decreasing_by
  · simp [SignalType.complexity]
  · have smaller := SignalTypes.complexity_typeAt_lt
      fields component
    exact smaller

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  namingForType signalType (.positional signalType)

/-- Apply authored names only to the emitted register boundary. Recursive
splitters, combiners, and component registers retain canonical positional
naming. -/
def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.Register.moduleStructure signalType) :=
  (naming signalType).withPorts (portsWithNaming signalType typeNaming)

end Silean.Modules.Register.Naming

namespace Silean.Modules.Register

/-! ## Complete designs -/

/-- The canonical register structure paired with caller-supplied emitted names. -/
def designWith {signalType : SignalType}
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType
  naming := Naming.namingWith signalType typeNaming

/-- The generic register structure paired with its default recursive naming. -/
def design (signalType : SignalType) : Silean.Naming.NamedModule :=
  designWith (Naming.SignalTypeNaming.positional signalType)

/-! ## Placement -/

open Silean.Authoring.CircuitDescription

/-- Place a register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (value : Net signalType) : Builder (Net signalType) := do
  let child <- Authoring.CircuitDescription.placeNamed name
    (design signalType) fun | .input => value
  pure (child .output)

/-- Place a register using the next conventional indexed name. -/
noncomputable def place (value : Net signalType) : Builder (Net signalType) := do
  let child <- placeIndexed "register" (design signalType) fun | .input => value
  pure (child .output)

end Silean.Modules.Register
