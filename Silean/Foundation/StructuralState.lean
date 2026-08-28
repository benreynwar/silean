import Silean.Foundation.SignalMap

namespace Silean

/-! Structural state mirrors the named instance hierarchy. -/

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

end Silean
