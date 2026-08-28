namespace Silean

/-! Structural signal shapes. Tuples are anonymous ordered products: symbolic
field identities are supplied by the same `SignalMap` abstraction later used
for module ports.

`SignalTypes` is the list-shaped half of this mutual definition. Although it
contains the same information as `List SignalType`, defining it mutually with
`SignalType` makes the recursive relationship between tuple shapes and their
fields explicit, simplifying dependent definitions and termination proofs. -/

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

end Silean
