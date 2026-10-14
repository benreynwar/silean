import Silean.Modules.AddSub.Internal.AddSubVerification

/-! Public placement and correctness declarations for selectable structural
addition and subtraction. -/

namespace Silean.Modules.AddSub

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) (subtract : Net .bit) :
    Builder (Net (.vector
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit)) := do
  let outputs ← ports.placeNamed leftWidth rightWidth leftSigned rightSigned
    extendOutput name
    (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming leftWidth rightWidth leftSigned rightSigned extendOutput)
    left right subtract
  pure outputs.result

noncomputable def place
    (leftSigned rightSigned extendOutput : Bool)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) (subtract : Net .bit) :
    Builder (Net (.vector
      (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit)) := do
  let outputs ← ports.placeIndexed leftWidth rightWidth leftSigned rightSigned
    extendOutput "add_sub"
    (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming leftWidth rightWidth leftSigned rightSigned extendOutput)
    left right subtract
  pure outputs.result

attribute [circuit_description] placeNamed place

theorem result_of_realization (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    {step : (moduleStructure leftWidth rightWidth leftSigned rightSigned
      extendOutput).Step}
    (realizes : (moduleStructure leftWidth rightWidth leftSigned rightSigned
      extendOutput).Realizes step) :
    step.outputs .result = resultValue leftWidth rightWidth leftSigned
      rightSigned extendOutput (step.inputs .left) (step.inputs .right)
        (step.inputs .subtract) := by
  obtain ⟨_, _, allowed⟩ := allowed_of_realization leftWidth rightWidth
    leftSigned rightSigned extendOutput realizes
  exact cycleContract.result leftWidth rightWidth leftSigned rightSigned
    extendOutput allowed

theorem implements_contract (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool) :
    Contracts.Cycle.Implements
      (moduleStructure leftWidth rightWidth leftSigned rightSigned extendOutput)
      (cycleContract leftWidth rightWidth leftSigned rightSigned extendOutput)
      (certification leftWidth rightWidth leftSigned rightSigned
        extendOutput).stateCorresponds :=
  (certification leftWidth rightWidth leftSigned rightSigned
    extendOutput).implements

end Silean.Modules.AddSub
