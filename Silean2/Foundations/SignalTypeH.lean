namespace Silean2.Foundations

mutual
  inductive SignalType
  | bit
  | vector (length : Nat) (element : SignalType)
  | tuple (fields : SignalTypes)
  deriving DecidableEq, Repr

  inductive SignalTypes
  | nil
  | cons (head : SignalType) (tail : SignalTypes)
  deriving DecidableEq, Repr
end

mutual
  def SignalType.Denote : SignalType → Type
  | .bit => Bool
  | .vector length element => Fin length → element.Denote
  | .tuple fields => fields.Denote

  def SignalTypes.Denote : SignalTypes → Type
  | .nil => Unit
  | .cons head tail => head.Denote × tail.Denote
end

end Silean2.Foundations
