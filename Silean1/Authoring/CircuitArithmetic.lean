import Silean.Authoring.CircuitLogic
import Silean.Modules.Add.AddDerived
import Silean.Modules.AddSub.AddSubDerived
import Silean.Modules.Sub.SubDerived

/-! Fixed-width arithmetic placement syntax for circuit descriptions.

The suffixes on `+uu`, `+us`, `+su`, `+ss` and their subtraction counterparts
state whether the left and right operands are interpreted as unsigned (`u`) or
signed (`s`). These forms produce one more bit than the larger input. Appending
`t`, as in `+ust`, selects a truncating form whose result has the larger input
width. Each form places one genuine certified `Add` or `Sub` module. Results
remain plain bit-vector nets, so each later arithmetic operation chooses its
operand interpretations afresh.
-/

namespace Silean.Authoring

open Silean
open CircuitDescription

/-- Place addition with independently selected operand interpretations. -/
noncomputable def addWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth + 1) .bit)) :=
  Modules.Add.place leftSigned rightSigned true left right

/-- Place subtraction with independently selected operand interpretations. -/
noncomputable def subtractWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth + 1) .bit)) :=
  Modules.Sub.place leftSigned rightSigned true left right

/-- Place truncating addition with independently selected operand
interpretations. -/
noncomputable def addTruncatingWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth) .bit)) :=
  Modules.Add.place leftSigned rightSigned false left right

/-- Place truncating subtraction with independently selected operand
interpretations. -/
noncomputable def subtractTruncatingWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (max leftWidth rightWidth) .bit)) :=
  Modules.Sub.place leftSigned rightSigned false left right

/-- Place runtime-selectable extended addition/subtraction. -/
noncomputable def addSubWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) (subtract : Net .bit) :
    Builder (Net (.vector (max leftWidth rightWidth + 1) .bit)) :=
  Modules.AddSub.place leftSigned rightSigned true left right subtract

/-- Place runtime-selectable truncating addition/subtraction. -/
noncomputable def addSubTruncatingWith (leftSigned rightSigned : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) (subtract : Net .bit) :
    Builder (Net (.vector (max leftWidth rightWidth) .bit)) :=
  Modules.AddSub.place leftSigned rightSigned false left right subtract

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
  addWith subtractWith addTruncatingWith subtractTruncatingWith
  addSubWith addSubTruncatingWith
  addUU addUS addSU addSS subtractUU subtractUS subtractSU subtractSS
  addUUT addUST addSUT addSST
  subtractUUT subtractUST subtractSUT subtractSST

end Silean.Authoring
