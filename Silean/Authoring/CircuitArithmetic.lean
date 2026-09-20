import Silean.Authoring.CircuitLogic
import Silean.Modules.Add.AddDerived
import Silean.Modules.AddSub.AddSubDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived

/-! Fixed-width arithmetic for circuit descriptions.

The suffixes on `+uu`, `+us`, `+su`, `+ss` and their subtraction counterparts
state whether the left and right operands are interpreted as unsigned (`u`) or
signed (`s`). These forms produce one more bit than the larger input. Appending
`t`, as in `+ust`, selects a truncating form whose result has the larger input
width. Results remain plain bit-vector nets, so each later arithmetic operation
chooses its operand interpretations afresh.
-/

namespace Silean.Authoring

open Silean
open CircuitDescription

/-- Extend an LSB-first vector, copying its sign bit when `signed` is true and
filling with zero otherwise. A zero-width input always extends with zero. -/
def extendLayout (signed : Bool) : (inputWidth outputWidth : Nat) →
    Fin outputWidth → Modules.VectorLayout.BitSource inputWidth
  | 0, _ => fun _ => .constant false
  | inputWidth + 1, _ => fun index =>
      if withinInput : index.val < inputWidth + 1 then
        .input ⟨index.val, withinInput⟩
      else if signed then
        .input (Fin.last inputWidth)
      else
        .constant false

/-- Extend a vector net, avoiding an identity layout when its width already
matches the requested width. -/
noncomputable def extend (signed : Bool) (outputWidth : Nat)
    (value : Net (.vector inputWidth .bit)) :
    Builder (Net (.vector outputWidth .bit)) :=
  if sameWidth : inputWidth = outputWidth then
    pure (sameWidth ▸ value)
  else
    Modules.VectorLayout.place
      (extendLayout signed inputWidth outputWidth) value

/-- Place addition at a caller-selected result width. -/
noncomputable def addAtWidth (leftSigned rightSigned : Bool)
    (resultWidth : Nat) (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector resultWidth .bit)) := do
  let extendedLeft ← extend leftSigned resultWidth left
  let extendedRight ← extend rightSigned resultWidth right
  let carryIn ← constant .bit false
  pure (← Modules.Add.place extendedLeft extendedRight carryIn).result

/-- Place subtraction at a caller-selected result width. -/
noncomputable def subtractAtWidth (leftSigned rightSigned : Bool)
    (resultWidth : Nat) (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector resultWidth .bit)) := do
  let extendedLeft ← extend leftSigned resultWidth left
  let extendedRight ← extend rightSigned resultWidth right
  let subtractMode ← constant .bit true
  pure (← Modules.AddSub.place extendedLeft extendedRight subtractMode).result

/-- Place addition with independently selected operand interpretations. -/
noncomputable def addWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth + 1) .bit)) :=
  addAtWidth leftSigned rightSigned (max leftWidth rightWidth + 1) left right

/-- Place subtraction with independently selected operand interpretations. -/
noncomputable def subtractWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth + 1) .bit)) :=
  subtractAtWidth leftSigned rightSigned
    (max leftWidth rightWidth + 1) left right

/-- Place truncating addition with independently selected operand
interpretations. -/
noncomputable def addTruncatingWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth) .bit)) :=
  addAtWidth leftSigned rightSigned (max leftWidth rightWidth) left right

/-- Place truncating subtraction with independently selected operand
interpretations. -/
noncomputable def subtractTruncatingWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth) .bit)) :=
  subtractAtWidth leftSigned rightSigned
    (max leftWidth rightWidth) left right

noncomputable abbrev addUU (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := addWith false false left right
noncomputable abbrev addUS (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := addWith false true left right
noncomputable abbrev addSU (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := addWith true false left right
noncomputable abbrev addSS (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := addWith true true left right
noncomputable abbrev subtractUU (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := subtractWith false false left right
noncomputable abbrev subtractUS (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := subtractWith false true left right
noncomputable abbrev subtractSU (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := subtractWith true false left right
noncomputable abbrev subtractSS (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) := subtractWith true true left right
noncomputable abbrev addUUT (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  addTruncatingWith false false left right
noncomputable abbrev addUST (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  addTruncatingWith false true left right
noncomputable abbrev addSUT (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  addTruncatingWith true false left right
noncomputable abbrev addSST (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  addTruncatingWith true true left right
noncomputable abbrev subtractUUT (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  subtractTruncatingWith false false left right
noncomputable abbrev subtractUST (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  subtractTruncatingWith false true left right
noncomputable abbrev subtractSUT (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  subtractTruncatingWith true false left right
noncomputable abbrev subtractSST (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :=
  subtractTruncatingWith true true left right

scoped infixl:65 " +uu " => addUU
scoped infixl:65 " +us " => addUS
scoped infixl:65 " +su " => addSU
scoped infixl:65 " +ss " => addSS
scoped infixl:65 " -uu " => subtractUU
scoped infixl:65 " -us " => subtractUS
scoped infixl:65 " -su " => subtractSU
scoped infixl:65 " -ss " => subtractSS
scoped infixl:65 " +uut " => addUUT
scoped infixl:65 " +ust " => addUST
scoped infixl:65 " +sut " => addSUT
scoped infixl:65 " +sst " => addSST
scoped infixl:65 " -uut " => subtractUUT
scoped infixl:65 " -ust " => subtractUST
scoped infixl:65 " -sut " => subtractSUT
scoped infixl:65 " -sst " => subtractSST

attribute [circuit_description]
  extendLayout extend addAtWidth subtractAtWidth addWith subtractWith
  addTruncatingWith subtractTruncatingWith
  addUU addUS addSU addSS subtractUU subtractUS subtractSU subtractSS
  addUUT addUST addSUT addSST
  subtractUUT subtractUST subtractSUT subtractSST

end Silean.Authoring
