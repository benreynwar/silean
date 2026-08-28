import Silean.Foundation.SignalMap

namespace Silean

/-! Structural state mirrors the named instance hierarchy. -/

inductive StructuralState : Type 1 where
  | leaf (signals : SignalMap)
  | children (states : EnumeratedMap StructuralState)

def StructuralState.Values : StructuralState → Type
  | .leaf signals => signals.Values
  | .children states => (name : states.Key) → (states.value name).Values

def StructuralState.defaultValues : (state : StructuralState) → state.Values
  | .leaf signals => signals.defaultValues
  | .children states => fun name => (states.value name).defaultValues

end Silean
