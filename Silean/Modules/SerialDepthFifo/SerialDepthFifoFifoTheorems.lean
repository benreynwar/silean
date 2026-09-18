import Silean.Modules.SerialDepthFifo.Internal.SerialDepthFifoFifoVerification

/-! # Serial-depth FIFO refinement theorems

The proof recursively lifts the one-entry FIFO refinement through generic
serial composition. Its public result is a certified FIFO of the requested
positive capacity; recursive proof helpers remain private or under
`SerialDepthFifo.Internal`.
-/

namespace Silean.Modules.SerialDepthFifo

open Silean
noncomputable def fifoCertified (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element)
      (Silean.Interfaces.Fifo.payloadTypes element) :=
  Internal.fifoCertified element depth positive

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).moduleStructure =
      moduleStructure element depth positive := by
  exact Internal.fifoCertified_moduleStructure element depth positive

@[simp] theorem fifoCertified_contract (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).contract =
      Silean.Contracts.Fifo.standardContract element depth := by
  exact Internal.fifoCertified_contract element depth positive

end Silean.Modules.SerialDepthFifo
