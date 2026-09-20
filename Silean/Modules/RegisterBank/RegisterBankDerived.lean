import Silean.Modules.RegisterBank.Internal.RegisterBankVerification

/-! Public register-bank declarations backed by generated internals. -/

namespace Silean.Modules.RegisterBank

open Silean
open Authoring.CircuitDescription

/-- Read ports produced by a placed register bank. -/
structure PlacedOutputs (element : SignalType) (readCount : Nat) where
  readValue : Fin readCount → Net element

/-- Place a register bank under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (writeEnable : Net .bit) (writeAddress : Net (.vector addressWidth .bit))
    (writeValue : Net element)
    (readAddress : Fin readCount → Net (.vector addressWidth .bit)) :
    Builder (PlacedOutputs element readCount) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design element addressWidth readCount) fun
      | .writeEnable => writeEnable
      | .writeAddress => writeAddress
      | .writeValue => writeValue
      | .readAddress port => readAddress port
  pure { readValue := fun port => child (.readValue port) }

/-- Place a register bank using the next conventional indexed name. -/
noncomputable def place
    (writeEnable : Net .bit) (writeAddress : Net (.vector addressWidth .bit))
    (writeValue : Net element)
    (readAddress : Fin readCount → Net (.vector addressWidth .bit)) :
    Builder (PlacedOutputs element readCount) := do
  let child ← placeIndexed "register_bank"
    (design element addressWidth readCount) fun
      | .writeEnable => writeEnable
      | .writeAddress => writeAddress
      | .writeValue => writeValue
      | .readAddress port => readAddress port
  pure { readValue := fun port => child (.readValue port) }

attribute [circuit_description] placeNamed place

/-- The generated register-bank hierarchy implements its exact contract. -/
theorem implements_contract (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure element addressWidth readCount)
      (cycleContract element addressWidth readCount)
      (certification element addressWidth readCount).stateCorresponds :=
  (certification element addressWidth readCount).implements

end Silean.Modules.RegisterBank
