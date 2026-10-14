import Silean.Modules.BitMux.BitMuxDerived
import Silean.Modules.Mux.MuxDerived

/-! Concise selection vocabulary for circuit descriptions.

This sits above the mux modules because those modules themselves use the
lower-level Boolean vocabulary in `CircuitLogic.lean`.
-/

namespace Silean.Authoring

open Silean
open CircuitDescription

/-- Selects the hardware used by `mux` from the selected signal type. -/
class MuxPlacement (signalType : SignalType) where
  place : Net .bit → Net signalType → Net signalType → Builder (Net signalType)

/-- Selecting between two bits uses the compact gate-level bit mux. -/
noncomputable instance (priority := 200) : MuxPlacement .bit where
  place := Modules.BitMux.place

/-- Selecting between aggregate values uses the recursive generic mux. -/
noncomputable instance (priority := 100) (signalType : SignalType) :
    MuxPlacement signalType where
  place := Modules.Mux.place

/-- Select `whenTrue` when `select` is high and `whenFalse` otherwise.

The result type chooses between the bit-specific and generic mux modules. -/
noncomputable def mux [operation : MuxPlacement signalType]
    (select : Net .bit) (whenFalse whenTrue : Net signalType) :
    Builder (Net signalType) :=
  operation.place select whenFalse whenTrue

attribute [circuit_description] mux MuxPlacement.place

end Silean.Authoring
