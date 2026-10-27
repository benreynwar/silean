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

def checkedCast
    {F : SignalType → Type}
    (expectedType : SignalType)
    {actualType : SignalType}
    (value : F actualType)
    : Except String (F expectedType) :=
  if h : actualType = expectedType then
    pure (h ▸ value)
  else
    throw s!"Type mismatch, expected type is {repr expectedType} but seen type is {repr actualType}"


end Silean2.Foundations
