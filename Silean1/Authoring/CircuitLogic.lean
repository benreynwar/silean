import Silean.Authoring.CircuitDescription
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.Constant.Constant
import Silean.Modules.Mask.Mask
import Silean.Modules.Equality.EqualityDerived
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.And
import Silean.Primitives.Eq
import Silean.Primitives.Not
import Silean.Primitives.Xor

/-! Scoped notation for placing combinational logic in a circuit description.
The extra operator character distinguishes builder actions from Lean's pure
Boolean operations: `!!`, `&&&`, `^^^`, and `|||` place hardware.
-/

namespace Silean.Authoring

open Silean
open CircuitDescription

/-- Place a constant source. This short spelling is part of the opt-in
authoring vocabulary; the owning module's explicit API is `Constant.place`. -/
noncomputable abbrev constant (signalType : SignalType)
    (value : signalType.Denote) : Builder (Net signalType) :=
  Modules.Constant.place signalType value

/-- Split an aggregate into its immediate structural components using a
conventional indexed instance name. -/
noncomputable def split : (splitter : Composition.SignalSplitter) →
    Net splitter.aggregateType →
    Builder ((output : splitter.ports.outputs.Label) →
      Net (splitter.ports.outputs.signalType output))
  | .vector length elementType, value => do
      let child ← placeIndexed "splitter"
        (Naming.SignalAdapter.splitterDesign (.vector length elementType)) fun
          | .value => value
      pure child
  | .tuple fields, value => do
      let child ← placeIndexed "splitter"
        (Naming.SignalAdapter.splitterDesign (.tuple fields)) fun
          | .value => value
      pure child

/-- Split an aggregate under an explicit structural instance name. -/
noncomputable def splitNamed (name : Naming.SourceName) :
    (splitter : Composition.SignalSplitter) → Net splitter.aggregateType →
    Builder ((output : splitter.ports.outputs.Label) →
      Net (splitter.ports.outputs.signalType output))
  | .vector length elementType, value => do
      let child ← CircuitDescription.placeNamed name
        (Naming.SignalAdapter.splitterDesign (.vector length elementType)) fun
          | .value => value
      pure child
  | .tuple fields, value => do
      let child ← CircuitDescription.placeNamed name
        (Naming.SignalAdapter.splitterDesign (.tuple fields)) fun
          | .value => value
      pure child

/-- Combine immediate structural components using a conventional indexed
instance name. -/
noncomputable def combine : (combiner : Composition.SignalCombiner) →
    ((input : combiner.ports.inputs.Label) →
      Net (combiner.ports.inputs.signalType input)) →
    Builder (Net combiner.aggregateType)
  | .vector length elementType, values => do
      let child ← placeIndexed "combiner"
        (Naming.SignalAdapter.combinerDesign (.vector length elementType)) values
      pure (child .value)
  | .tuple fields, values => do
      let child ← placeIndexed "combiner"
        (Naming.SignalAdapter.combinerDesign (.tuple fields)) values
      pure (child .value)

/-- Combine immediate structural components under an explicit instance name. -/
noncomputable def combineNamed (name : Naming.SourceName) :
    (combiner : Composition.SignalCombiner) →
    ((input : combiner.ports.inputs.Label) →
      Net (combiner.ports.inputs.signalType input)) →
    Builder (Net combiner.aggregateType)
  | .vector length elementType, values => do
      let child ← CircuitDescription.placeNamed name
        (Naming.SignalAdapter.combinerDesign (.vector length elementType)) values
      pure (child .value)
  | .tuple fields, values => do
      let child ← CircuitDescription.placeNamed name
        (Naming.SignalAdapter.combinerDesign (.tuple fields)) values
      pure (child .value)

/-- Selects the hardware used by `&&&` from its operand signal types. -/
class AndPlacement (leftType rightType : SignalType) where
  place : Net leftType → Net rightType → Builder (Net leftType)

/-- Two concrete bits use the primitive AND gate. This most-specific case has
priority over both more general forms below. -/
instance (priority := 300) bitAndPlacement : AndPlacement .bit .bit where
  place := Primitives.And.place

/-- A single bit on the right masks every bit of the value on the left. -/
noncomputable instance (priority := 200) maskAndPlacement (signalType : SignalType) :
    AndPlacement signalType .bit where
  place := Modules.Mask.place

/-- Equally typed values use recursive bitwise AND. -/
noncomputable instance (priority := 100) bitwiseAndPlacement (signalType : SignalType) :
    AndPlacement signalType signalType where
  place := Modules.BitwiseAnd.place

noncomputable def placeAnd [operation : AndPlacement leftType rightType]
    (left : Net leftType) (right : Net rightType) : Builder (Net leftType) :=
  operation.place left right

/-- Selects the hardware used by `^^^` from its operand signal type. -/
class XorPlacement (signalType : SignalType) where
  place : Net signalType → Net signalType → Builder (Net signalType)

/-- Two concrete bits use the primitive XOR gate. -/
instance (priority := 200) : XorPlacement .bit where
  place := Primitives.Xor.place

/-- Equally typed aggregate values use recursive bitwise XOR. -/
noncomputable instance (priority := 100) (signalType : SignalType) :
    XorPlacement signalType where
  place := Modules.BitwiseXor.place

noncomputable def placeXor [operation : XorPlacement signalType]
    (left right : Net signalType) : Builder (Net signalType) :=
  operation.place left right

/-- Selects the hardware used by `|||` from its operand signal type. -/
class OrPlacement (signalType : SignalType) where
  place : Net signalType → Net signalType → Builder (Net signalType)

/-- Two concrete bits use the primitive OR gate. -/
instance (priority := 200) : OrPlacement .bit where
  place := Primitives.Or.place

/-- Equally typed aggregate values use recursive bitwise OR. -/
noncomputable instance (priority := 100) (signalType : SignalType) :
    OrPlacement signalType where
  place := Modules.BitwiseOr.place

noncomputable def placeOr [operation : OrPlacement signalType]
    (left right : Net signalType) : Builder (Net signalType) :=
  operation.place left right

/-- Selects the hardware used by `===` from its operand signal type. -/
class EqPlacement (signalType : SignalType) where
  place : Net signalType → Net signalType → Builder (Net .bit)

/-- Two concrete bits use the primitive equality gate. -/
instance (priority := 200) bitEqPlacement : EqPlacement .bit where
  place := Primitives.Eq.place

/-- Equally typed aggregate values use recursive structural equality. -/
noncomputable instance (priority := 100) structuralEqPlacement (signalType : SignalType) :
    EqPlacement signalType where
  place := Modules.Equality.place

noncomputable def placeEq [operation : EqPlacement signalType]
    (left right : Net signalType) : Builder (Net .bit) :=
  operation.place left right

scoped prefix:75 "!! " => Primitives.Not.place
scoped infixl:65 " &&& " => placeAnd
scoped infixl:62 " ^^^ " => placeXor
scoped infixl:60 " ||| " => placeOr
scoped infix:50 " === " => placeEq

attribute [circuit_description]
  constant split splitNamed combine combineNamed
  placeAnd AndPlacement.place placeXor XorPlacement.place
  placeOr OrPlacement.place placeEq EqPlacement.place
  Modules.Constant.place Modules.Equality.place Modules.Mask.place
  Modules.BitwiseAnd.place Modules.BitwiseOr.place Modules.BitwiseXor.place
  Primitives.And.place Primitives.Or.place Primitives.Xor.place
  Primitives.Eq.place Primitives.Not.place

end Silean.Authoring
