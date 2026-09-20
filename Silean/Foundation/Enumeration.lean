import Lean

namespace Silean

/-! `enumeration` is the opt-in simplifier set for reducing concrete finite
label types to their ordered constructor lists. Keeping this separate from the
global simp set lets dependent structural proofs choose when lists should be
expanded. -/

register_simp_attr enumeration

/-! Constructive positions and finite executable enumerations. -/

/-! ## List indices -/

/-- A computational path to `value` in a list. Unlike ordinary membership in
`Prop`, it records a position that can drive dependent lookup. -/
inductive ListIndex {α : Type u} (value : α) : List α → Type u
  | head : ListIndex value (value :: rest)
  | tail : ListIndex value rest → ListIndex value (other :: rest)

/-- `"data"` occurs after one other element in this list. -/
example : ListIndex "data" ["enable", "data"] := .tail .head

/-- The first element is represented directly by `head`. -/
example : ListIndex "enable" ["enable", "data"] := .head

namespace ListIndex

/-- Recover a computational list position from ordinary membership when the
element type has decidable equality. This is useful at proof/execution
boundaries where a propositionally checked schedule must drive dependent
lookup. -/
noncomputable def ofMem {α : Type u} [DecidableEq α]
    {value : α} {values : List α}
    (member : value ∈ values) : ListIndex value values := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      if equal : value = head then
        subst head
        exact .head
      else
        exact .tail (induction (by simpa [equal] using member))

@[simp] theorem ofMem_cons_self {α : Type u} [DecidableEq α]
    (value : α) (values : List α)
    (member : value ∈ value :: values) :
    ofMem member = (.head : ListIndex value (value :: values)) := by
  simp [ofMem]

theorem ofMem_cons_of_ne {α : Type u} [DecidableEq α]
    {value head : α} {values : List α} (different : value ≠ head)
    (member : value ∈ values) :
    ofMem (List.mem_cons_of_mem head member) =
      (.tail (ofMem member) : ListIndex value (head :: values)) := by
  simp [ofMem, different]

def map {α : Type u} {β : Type v} (transform : α → β)
    {value : α} {values : List α} :
    ListIndex value values → ListIndex (transform value) (values.map transform)
  | .head => .head
  | .tail index => .tail (index.map transform)

def appendRight {α : Type u} {value : α} {values : List α}
    (suffix : List α) : ListIndex value values →
    ListIndex value (values ++ suffix)
  | .head => .head
  | .tail index => .tail (index.appendRight suffix)

def prependMany {α : Type u} {value : α} {values : List α}
    (preceding : List α) (index : ListIndex value values) :
    ListIndex value (preceding ++ values) :=
  match preceding with
  | [] => index
  | _ :: rest => .tail (index.prependMany rest)

def finRange : (index : Fin width) → ListIndex index (List.finRange width) := by
  induction width with
  | zero => exact fun index => Fin.elim0 index
  | succ width induction =>
      intro index
      rw [List.finRange_succ]
      refine Fin.cases .head (fun tail => .tail ?_) index
      exact (induction tail).map Fin.succ

def toFin {α : Type u} {value : α} {values : List α} :
    ListIndex value values → Fin values.length
  | .head => 0
  | .tail index => index.toFin.succ

/-- Forget the computational position and recover ordinary list membership. -/
theorem mem {α : Type u} {value : α} {values : List α}
    (index : ListIndex value values) : value ∈ values := by
  induction index with
  | head => simp
  | tail _ member => exact List.mem_cons_of_mem _ member

theorem get_eq {α : Type u} {value : α} {values : List α}
    (index : ListIndex value values) : values[index.toFin] = value := by
  induction index with
  | head => rfl
  | tail _ induction => exact induction

/-- The witness can be used as a bounded index and retrieves the value named
in its type. -/
example :
    let index : ListIndex "data" ["enable", "data"] := .tail .head
    index.toFin.val = 1 := rfl

example :
    let index : ListIndex "data" ["enable", "data"] := .tail .head
    ["enable", "data"][index.toFin] = "data" := rfl

theorem get_map_eq {α : Type u} {β : Type v}
    {value : α} {values : List α} (index : ListIndex value values)
    (transform : α → β) :
    (values.map transform)[index.toFin.val]'(by simp) = transform value := by
  rw [List.getElem_map]
  exact congrArg transform index.get_eq

/-- A value has only one position in a duplicate-free list. -/
theorem eq_of_nodup {α : Type u} {value : α} {values : List α}
    (nodup : values.Nodup) (left right : ListIndex value values) :
    left = right := by
  induction left with
  | head =>
      cases right with
      | head => rfl
      | tail right =>
          exact False.elim ((List.nodup_cons.mp nodup).1 right.mem)
  | tail left induction =>
      cases right with
      | head =>
          exact False.elim ((List.nodup_cons.mp nodup).1 left.mem)
      | tail right =>
          congr
          exact induction (List.nodup_cons.mp nodup).2 right

end ListIndex

/-! ## Dependent lists -/

/-- Values corresponding to a list of keys, where the value type may depend on
the key. A `ListIndex` selects a key and permits lookup at its `Value key` type. -/
inductive DependentList {α : Type u} (Value : α → Type v) : List α → Type (max u v)
  | nil : DependentList Value []
  | cons (head : Value key) (tail : DependentList Value keys) :
      DependentList Value (key :: keys)

/-- This list contains a `Nat` at key `false` and a `String` at key `true`. -/
example : DependentList (fun
    | false => Nat
    | true => String) [false, true] :=
  .cons 32 (.cons "ready" .nil)

/-- The empty key list carries no values. -/
example : DependentList (fun _ : Bool => Nat) [] := .nil

namespace DependentList

def get {α : Type u} {Value : α → Type v} {keys : List α}
    (values : DependentList Value keys) {key : α} :
    ListIndex key keys → Value key
  | .head => match values with | .cons head _ => head
  | .tail index => match values with | .cons _ tail => tail.get index

/-- Lookup returns the type selected by the key. -/
example :
    let Value : Bool → Type := fun
      | false => Nat
      | true => String
    let values : DependentList Value [false, true] :=
      .cons 32 (.cons "ready" .nil)
    values.get (.head : ListIndex false [false, true]) = 32 := rfl

example :
    let Value : Bool → Type := fun
      | false => Nat
      | true => String
    let values : DependentList Value [false, true] :=
      .cons 32 (.cons "ready" .nil)
    values.get (.tail .head : ListIndex true [false, true]) = "ready" := rfl

theorem exists_of_forall_exists {α : Type u} {Value : α → Type v}
    (Property : (key : α) → Value key → Prop)
    (available : ∀ key, ∃ value, Property key value) :
    ∀ keys : List α, ∃ values : DependentList Value keys,
      ∀ key (index : ListIndex key keys), Property key (values.get index)
  | [] => ⟨.nil, fun _ index => nomatch index⟩
  | key :: keys => by
      rcases available key with ⟨head, headProperty⟩
      rcases exists_of_forall_exists Property available keys with
        ⟨tail, tailProperty⟩
      refine ⟨.cons head tail, ?_⟩
      intro selected index
      cases index with
      | head => exact headProperty
      | tail index => exact tailProperty selected index

end DependentList

/-! ## Supporting list theorems -/

namespace List

/-- A member's mapped list occurs as a sublist of the flattened family. -/
theorem sublist_flatMap_of_mem {values : List α} {value : α}
    (transform : α → List β) (member : value ∈ values) :
    (transform value).Sublist (values.flatMap transform) := by
  induction values with
  | nil => cases member
  | cons head tail induction =>
      rcases List.mem_cons.mp member with equal | member
      · subst head
        exact List.sublist_append_left _ _
      · exact (induction member).trans
          (List.sublist_append_right (transform head) _)

/-- In a duplicate-free flattened family, two member lists containing the same
value must come from the same outer member. -/
theorem eq_of_mem_of_mem_of_flatMap_nodup
    {values : List α} (transform : α → List β)
    (nodup : (values.flatMap transform).Nodup)
    {left right : α} (leftMem : left ∈ values) (rightMem : right ∈ values)
    {value : β} (inLeft : value ∈ transform left)
    (inRight : value ∈ transform right) : left = right := by
  induction values generalizing left right value with
  | nil => cases leftMem
  | cons head tail induction =>
      have parts := List.nodup_append.mp nodup
      rcases List.mem_cons.mp leftMem with leftEqual | leftTail
      · subst left
        rcases List.mem_cons.mp rightMem with rightEqual | rightTail
        · exact rightEqual.symm
        · exfalso
          exact parts.2.2 value inLeft value
            (List.mem_flatMap.mpr ⟨right, rightTail, inRight⟩) rfl
      · rcases List.mem_cons.mp rightMem with rightEqual | rightTail
        · subst right
          exfalso
          exact parts.2.2 value inRight value
            (List.mem_flatMap.mpr ⟨left, leftTail, inLeft⟩) rfl
        · exact induction parts.2.1 leftTail rightTail inLeft inRight

theorem nodup_map_of_injective (transform : α → β)
    (injective : Function.Injective transform) :
    ∀ {values : List α}, values.Nodup → (values.map transform).Nodup
  | [], _ => .nil
  | head :: tail, .cons fresh tailNodup => by
      rw [List.map_cons]
      apply List.Pairwise.cons
      · intro value membership equal
        rcases List.mem_map.mp membership with ⟨source, sourceMem, rfl⟩
        exact fresh source sourceMem (injective equal.symm).symm
      · exact nodup_map_of_injective transform injective tailNodup

theorem finRange_nodup : ∀ width, (List.finRange width).Nodup
  | 0 => .nil
  | width + 1 => by
      rw [List.finRange_succ]
      apply List.Pairwise.cons
      · intro value membership zeroEqualValue
        rcases List.mem_map.mp membership with ⟨index, _, indexEqualValue⟩
        have impossible := congrArg Fin.val
          (zeroEqualValue.trans indexEqualValue.symm)
        exact Nat.noConfusion impossible
      · exact nodup_map_of_injective Fin.succ
          (by intro left right equal; exact Fin.succ_inj.mp equal)
          (finRange_nodup width)

end List

/-! ## Enumerations -/

/-- An ordered list containing every value of `α` exactly once. In practice,
this turns finite symbolic types, especially inductive label types, into lists
that can be traversed and indexed. `locate` constructively witnesses that no
value is omitted. -/
class Enumeration (α : Type u) where
  values : List α
  nodup : values.Nodup
  locate : (value : α) → ListIndex value values

/- The supporting declarations are private: they exist only to make the
examples compile and cannot be used as library API. -/

private inductive ExamplePort
  | enable
  | data

@[reducible] private def examplePorts : Enumeration ExamplePort where
  values := [.enable, .data]
  nodup := by simp
  locate
    | .enable => .head
    | .data => .tail .head

/-- A hand-written enumeration fixes the traversal order and provides the
position of every value. Most label types use `deriving Enumeration` from the
downstream `DeriveEnumeration` module instead. -/
example : examplePorts.values = [.enable, .data] := rfl

example : (examplePorts.locate .data).toFin.val = 1 := rfl

namespace Enumeration

@[reducible] def fin (width : Nat) : Enumeration (Fin width) where
  values := List.finRange width
  nodup := List.finRange_nodup width
  locate := ListIndex.finRange

example : (Enumeration.fin 3).values = [0, 1, 2] := rfl

@[reducible] def punit : Enumeration PUnit where
  values := [.unit]
  nodup := by simp
  locate | .unit => .head

@[reducible] def sum (left : Enumeration α) (right : Enumeration β) :
    Enumeration (Sum α β) where
  values := left.values.map Sum.inl ++ right.values.map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_map_of_injective Sum.inl ?_ left.nodup,
      List.nodup_map_of_injective Sum.inr ?_ right.nodup, ?_⟩
    · intro first second equal
      injection equal
    · intro first second equal
      injection equal
    · intro leftValue leftMem rightValue rightMem equal
      rcases List.mem_map.mp leftMem with ⟨source, _, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨source, _, rfl⟩
      cases equal
  locate
    | .inl value => (left.locate value).map Sum.inl |>.appendRight _
    | .inr value => (right.locate value).map Sum.inr |>.prependMany _

example : (Enumeration.sum examplePorts (Enumeration.fin 2)).values =
    [.inl .enable, .inl .data, .inr 0, .inr 1] := rfl

/-- Transport an executable enumeration across a pair of mutually inverse
functions. The source order is preserved exactly. -/
@[reducible] def relabel (source : Enumeration α) (forward : α → β)
    (backward : β → α) (leftInverse : Function.LeftInverse backward forward)
    (rightInverse : Function.RightInverse backward forward) : Enumeration β where
  values := source.values.map forward
  nodup := List.nodup_map_of_injective forward leftInverse.injective source.nodup
  locate value := by
    rw [← rightInverse value]
    exact (source.locate (backward value)).map forward

@[reducible] def ordinal (enumeration : Enumeration α) (value : α) :
    Fin enumeration.values.length := (enumeration.locate value).toFin

@[reducible] def empty (eliminate : α → False) : Enumeration α where
  values := []
  nodup := by simp
  locate value := False.elim (eliminate value)

theorem ordinal_injective (enumeration : Enumeration α) :
    Function.Injective enumeration.ordinal := by
  intro left right equal
  have leftAt := (enumeration.locate left).get_eq
  have rightAt := (enumeration.locate right).get_eq
  exact leftAt.symm.trans ((congrArg
    (fun index : Fin enumeration.values.length => enumeration.values[index])
    equal).trans rightAt)

def decidableEq (enumeration : Enumeration α) : DecidableEq α :=
  fun left right =>
    if equal : enumeration.ordinal left = enumeration.ordinal right then
      isTrue (enumeration.ordinal_injective equal)
    else
      isFalse fun valuesEqual => equal (congrArg enumeration.ordinal valuesEqual)

theorem exists_pi {Value : α → Type v}
    (enumeration : Enumeration α) (Property : (key : α) → Value key → Prop)
    (available : ∀ key, ∃ value, Property key value) :
    ∃ values : (key : α) → Value key, ∀ key, Property key (values key) := by
  rcases DependentList.exists_of_forall_exists Property available
      enumeration.values with ⟨values, properties⟩
  exact ⟨fun key => values.get (enumeration.locate key),
    fun key => properties key (enumeration.locate key)⟩

end Enumeration

/-! ## Enumerated maps -/

/-- A mapping that bundles its key type with a complete traversal order.
This allows structures to carry an otherwise-hidden finite key type while
still providing a value for, and permitting iteration over, every key. -/
structure EnumeratedMap (Value : Type v) where
  Key : Type u
  keys : Enumeration Key
  value : Key → Value

@[reducible] def EnumeratedMap.of (Key : Type u) [Enumeration Key]
    (value : Key → Value) : EnumeratedMap Value where
  Key := Key
  keys := inferInstance
  value := value

@[simp] theorem EnumeratedMap.of_value {Value : Type v} (KeyType : Type u)
    [Enumeration KeyType] (value : KeyType → Value) (key : KeyType) :
    (EnumeratedMap.of KeyType value).value key = value key := rfl

/- The private map below is checked documentation, not part of the public API. -/

private local instance : Enumeration ExamplePort := examplePorts

@[reducible] private def exampleWidths : EnumeratedMap Nat :=
  EnumeratedMap.of ExamplePort fun
    | .enable => 1
    | .data => 32

example : exampleWidths.value .enable = 1 := rfl

example : exampleWidths.value .data = 32 := rfl

def EnumeratedMap.orderedValues (map : EnumeratedMap Value) : List Value :=
  map.keys.values.map map.value

example : exampleWidths.orderedValues = [1, 32] := rfl

theorem EnumeratedMap.orderedValues_length (map : EnumeratedMap Value) :
    map.orderedValues.length = map.keys.values.length := by
  simp [orderedValues]

def EnumeratedMap.ordinal (map : EnumeratedMap Value) (key : map.Key) :
    Fin map.orderedValues.length :=
  ⟨(map.keys.ordinal key).val, by simp [orderedValues]⟩

theorem EnumeratedMap.value_at_ordinal (map : EnumeratedMap Value)
    (key : map.Key) : map.orderedValues[map.ordinal key] = map.value key := by
  exact (map.keys.locate key).get_map_eq map.value

example : exampleWidths.orderedValues[exampleWidths.ordinal .data] = 32 := rfl

end Silean
