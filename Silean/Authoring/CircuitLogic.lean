import Silean.Authoring.CircuitDescription
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.Mask.Mask
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Xor

/-! Scoped notation for placing combinational logic in a circuit description.
The extra operator character distinguishes builder actions from Lean's pure
Boolean operations: `!!`, `&&&`, `^^^`, and `|||` place hardware.
-/

namespace Silean.Authoring.CircuitLogic

open Silean
open CircuitDescription

/-- Selects the hardware used by `&&&` from its operand signal types. -/
class AndPlacement (leftType rightType : SignalType) where
  place : Net leftType → Net rightType → Builder (Net leftType)

/-- Two concrete bits use the primitive AND gate. This most-specific case has
priority over both more general forms below. -/
instance (priority := 300) : AndPlacement .bit .bit where
  place := Primitives.And.place

/-- A single bit on the right masks every bit of the value on the left. -/
noncomputable instance (priority := 200) (signalType : SignalType) :
    AndPlacement signalType .bit where
  place := Modules.Mask.place

/-- Equally typed values use recursive bitwise AND. -/
noncomputable instance (priority := 100) (signalType : SignalType) :
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

scoped prefix:75 "!! " => Primitives.Not.place
scoped infixl:65 " &&& " => placeAnd
scoped infixl:62 " ^^^ " => placeXor
scoped infixl:60 " ||| " => Modules.BitwiseOr.place

end Silean.Authoring.CircuitLogic
