import Silean.Modules.ROM.Internal.ROMVerification

/-! Public ROM declarations backed by the structural implementation. -/

namespace Silean.Modules.ROM

open Silean
open Authoring.CircuitDescription

/-- Place a ROM using separate caller-chosen definition and instance names. -/
noncomputable def placeNamed (definitionName : String)
    (instanceName : Naming.SourceName)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    (address : Net (.vector addressWidth .bit)) : Builder (Net element) := do
  let outputs ← ports.placeNamed element addressWidth instanceName
    (moduleStructure definitionName element addressWidth contents)
    (naming definitionName element addressWidth contents) address
  pure outputs.data

/-- Place a ROM under the next conventional instance name.  The explicit
definition name continues to identify its contents in emitted hardware. -/
noncomputable def place (definitionName : String)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    (address : Net (.vector addressWidth .bit)) : Builder (Net element) := do
  let outputs ← ports.placeIndexed element addressWidth "rom"
    (moduleStructure definitionName element addressWidth contents)
    (naming definitionName element addressWidth contents) address
  pure outputs.data

attribute [circuit_description] placeNamed place

/-- Every realizable ROM step performs the advertised table lookup. -/
theorem data_of_realization (definitionName : String) (element : SignalType)
    (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    {step : (moduleStructure definitionName element addressWidth contents).Step}
    (realizes :
      (moduleStructure definitionName element addressWidth contents).Realizes step) :
    step.outputs .data =
      lookup addressWidth contents (step.inputs .address) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification definitionName element addressWidth contents)
      |>.hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification definitionName element addressWidth contents)
      |>.allows_of_realizes contractState step corresponds realizes
  exact cycleContract.data element addressWidth contents allowed

/-- The generated constant-table and mux-tree hierarchy implements the exact
ROM lookup contract. -/
theorem implements_contract (definitionName : String) (element : SignalType)
    (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote) :
    Contracts.Cycle.Implements
      (moduleStructure definitionName element addressWidth contents)
      (cycleContract element addressWidth contents)
      (certification definitionName element addressWidth contents).stateCorresponds :=
  (certification definitionName element addressWidth contents).implements

end Silean.Modules.ROM
