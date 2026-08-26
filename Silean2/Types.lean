namespace Silean2

/-! Structural signal shapes. Tuples are anonymous ordered products: symbolic
field identities are supplied by the same `SignalMap` abstraction later used
for module ports. -/

mutual
  inductive SignalType where
    | bit
    | vector (length : Nat) (element : SignalType)
    | tuple (fields : SignalTypes)

  inductive SignalTypes where
    | nil
    | cons (head : SignalType) (tail : SignalTypes)
end

deriving instance DecidableEq for SignalType
deriving instance DecidableEq for SignalTypes
deriving instance Repr for SignalType
deriving instance Repr for SignalTypes

namespace SignalTypes

def ofList : List SignalType → SignalTypes
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def toList : SignalTypes → List SignalType
  | .nil => []
  | .cons head tail => head :: tail.toList

end SignalTypes

namespace SignalType

@[reducible] def tupleOfList (fields : List SignalType) : SignalType :=
  .tuple (SignalTypes.ofList fields)

end SignalType

mutual
  def SignalType.Denote : SignalType → Type
    | .bit => Bool
    | .vector length element => Fin length → element.Denote
    | .tuple fields => fields.Denote

  def SignalTypes.Denote : SignalTypes → Type
    | .nil => Unit
    | .cons head tail => head.Denote × tail.Denote
end

mutual
  def SignalType.default : (signalType : SignalType) → signalType.Denote
    | .bit => false
    | .vector _ element => fun _ => element.default
    | .tuple fields => fields.default

  def SignalTypes.default : (signalTypes : SignalTypes) → signalTypes.Denote
    | .nil => ()
    | .cons head tail => (head.default, tail.default)
end

/-! A simple measure for definitions that recurse from an aggregate signal
to one of its immediate component types. -/

mutual
  def SignalType.complexity : SignalType → Nat
    | .bit => 1
    | .vector _ element => element.complexity + 1
    | .tuple fields => fields.complexity + 1

  def SignalTypes.complexity : SignalTypes → Nat
    | .nil => 0
    | .cons head tail => head.complexity + tail.complexity + 1
end

/-! A constructive witness that a value occurs at a particular list position.
Unlike a proposition-only membership proof, it can be executed to recover the
position without search or choice. -/

inductive ListIndex {α : Type u} (value : α) : List α → Type u
  | head : ListIndex value (value :: rest)
  | tail : ListIndex value rest → ListIndex value (other :: rest)

namespace ListIndex

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

theorem get_eq {α : Type u} {value : α} {values : List α}
    (index : ListIndex value values) :
    values[index.toFin] = value := by
  induction index with
  | head => rfl
  | tail _ induction => exact induction

theorem get_map_eq {α : Type u} {β : Type v}
    {value : α} {values : List α} (index : ListIndex value values)
    (transform : α → β) :
    (values.map transform)[index.toFin.val]'(by simp) = transform value := by
  rw [List.getElem_map]
  exact congrArg transform index.get_eq

end ListIndex

/-! A constructive dependent tuple indexed by an ordinary list.  This lets
finite families assemble witnesses without any form of choice. -/

inductive DependentList {α : Type u} (Value : α → Type v) : List α → Type (max u v)
  | nil : DependentList Value []
  | cons (head : Value key) (tail : DependentList Value keys) :
      DependentList Value (key :: keys)

namespace DependentList

def get {α : Type u} {Value : α → Type v} {keys : List α}
    (values : DependentList Value keys) {key : α} :
    ListIndex key keys → Value key
  | .head => match values with | .cons head _ => head
  | .tail index => match values with | .cons _ tail => tail.get index

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

namespace List

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

/-! A finite executable enumeration. `locate` is completeness data in `Type`,
while `nodup` guarantees that the reported position is the only position for
that value. -/

class Enumeration (α : Type u) where
  values : List α
  nodup : values.Nodup
  locate : (value : α) → ListIndex value values

namespace Enumeration

@[reducible] def fin (width : Nat) : Enumeration (Fin width) where
  values := List.finRange width
  nodup := List.finRange_nodup width
  locate := ListIndex.finRange

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

inductive Framed (α : Type u)
  | start
  | item (value : α)
  | finish

@[reducible] def framed (inner : Enumeration α) : Enumeration (Framed α) where
  values := .start :: (inner.values.map Framed.item ++ [.finish])
  nodup := by
    apply List.Pairwise.cons
    · intro value member equal
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_map.mp member with ⟨source, _, rfl⟩
        cases equal
      · simp only [List.mem_singleton] at member
        cases member
        cases equal
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_map_of_injective Framed.item
        (by intro left right equal; cases equal; rfl) inner.nodup, by simp, ?_⟩
      intro left leftMem right rightMem equal
      rcases List.mem_map.mp leftMem with ⟨source, _, rfl⟩
      simp only [List.mem_singleton] at rightMem
      cases rightMem
      cases equal
  locate
    | .start => .head
    | .item value => .tail (ListIndex.appendRight [Framed.finish]
        ((inner.locate value).map Framed.item))
    | .finish => .tail (ListIndex.prependMany
        (inner.values.map Framed.item)
        (.head : ListIndex (Framed.finish : Framed α) [Framed.finish]))

def ordinal (enumeration : Enumeration α) (value : α) :
    Fin enumeration.values.length :=
  (enumeration.locate value).toFin

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

/-! A total map whose symbolic key type carries a canonical enumeration. This
is the shared representation behind signal labels, component instances, and
later finite symbolic tables. -/

structure EnumeratedMap (Value : Type v) where
  Key : Type u
  keys : Enumeration Key
  value : Key → Value

@[reducible] def EnumeratedMap.of (Key : Type u) [Enumeration Key]
    (value : Key → Value) : EnumeratedMap Value where
  Key := Key
  keys := inferInstance
  value := value

def EnumeratedMap.orderedValues (map : EnumeratedMap Value) : List Value :=
  map.keys.values.map map.value

theorem EnumeratedMap.orderedValues_length (map : EnumeratedMap Value) :
    map.orderedValues.length = map.keys.values.length := by
  simp [orderedValues]

def EnumeratedMap.ordinal (map : EnumeratedMap Value) (key : map.Key) :
    Fin map.orderedValues.length :=
  ⟨(map.keys.ordinal key).val, by
    simp [orderedValues]⟩

theorem EnumeratedMap.value_at_ordinal (map : EnumeratedMap Value)
    (key : map.Key) :
    map.orderedValues[map.ordinal key] = map.value key := by
  exact (map.keys.locate key).get_map_eq map.value

/-! A readable typed view of an ordered structural shape. `Label` is normally
an ordinary inductive type with constructors such as `.left` or `.valid`; it is
not an emitted string. `signalType` assigns each label its structural type.
Tuple fields and module ports use this same representation. -/

abbrev SignalMap := EnumeratedMap SignalType

abbrev SignalMap.Label (signalMap : SignalMap) := signalMap.Key

abbrev SignalMap.labels (signalMap : SignalMap) := signalMap.keys

abbrev SignalMap.signalType (signalMap : SignalMap) := signalMap.value

def SignalMap.types (signalMap : SignalMap) : List SignalType :=
  signalMap.orderedValues

def SignalMap.tupleType (signalMap : SignalMap) : SignalType :=
  .tupleOfList signalMap.types

abbrev SignalMap.Values (signalMap : SignalMap) :=
  (label : signalMap.Label) → (signalMap.signalType label).Denote

def SignalMap.defaultValues (signalMap : SignalMap) : signalMap.Values :=
  fun label => (signalMap.signalType label).default

def SignalMap.set (signalMap : SignalMap) (values : signalMap.Values)
    (label : signalMap.Label) (value : (signalMap.signalType label).Denote) :
    signalMap.Values := by
  letI : DecidableEq signalMap.Label := signalMap.labels.decidableEq
  intro other
  if equal : other = label then
    cases equal
    exact value
  else
    exact values other

@[simp] theorem SignalMap.set_same
    {signalMap : SignalMap} (values : signalMap.Values) (label : signalMap.Label)
    (value : (signalMap.signalType label).Denote) :
    SignalMap.set signalMap values label value label = value := by
  simp [set]

theorem SignalMap.set_other
    {signalMap : SignalMap} (values : signalMap.Values)
    (label other : signalMap.Label)
    (value : (signalMap.signalType label).Denote) (different : other ≠ label) :
    SignalMap.set signalMap values label value other = values other := by
  simp [set, different]

/-! The one canonical signal map with no labels. It is used for module state
when a module has no storage; combinational modules are not a separate kind. -/

inductive NoSignal

instance : Enumeration NoSignal :=
  Enumeration.empty fun signal => nomatch signal

def emptySignalMap : SignalMap :=
  EnumeratedMap.of NoSignal fun signal => nomatch signal

def SignalMap.emptyValues : emptySignalMap.Values :=
  fun signal => nomatch signal

/-! Structural state retains readable labels at every hierarchy level. A leaf
contains primitive-local state signals. A branch is labelled by its actual
child instance names and contains each child's complete structural state. -/

inductive StructuralState : Type 1 where
  | local (signals : SignalMap)
  | children (Name : Type) (names : Enumeration Name)
      (state : Name → StructuralState)

def StructuralState.Values : StructuralState → Type
  | .local signals => signals.Values
  | .children Name _ state => (name : Name) → (state name).Values

def StructuralState.defaultValues : (state : StructuralState) → state.Values
  | .local signals => signals.defaultValues
  | .children _ _ state => fun name => (state name).defaultValues

/-! A signature and its readable ports contain only connectivity. Structural
state is derived from a complete `ModuleStructure`, not stored in its port interface. -/

structure ModuleSignature where
  inputs : List SignalType
  outputs : List SignalType

structure ModulePorts where
  inputs : SignalMap
  outputs : SignalMap

def ModulePorts.signature (ports : ModulePorts) : ModuleSignature where
  inputs := ports.inputs.types
  outputs := ports.outputs.types

end Silean2
