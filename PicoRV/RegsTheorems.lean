import PicoRV.Internal.RegsVerification

/-! # PicoRV register-file theorems

This is the supported proof interface for the architectural register file.
The structural proof and its child hierarchy remain under `Internal/`.
-/

namespace PicoRV.Regs

open Silean

section AllowedStep

variable {step : cycleContract.Step} (allowed : cycleContract.Allows step)

include allowed

/-- The first read port returns register zero as zero and otherwise reads the
selected architectural register. -/
theorem cpuregs_rs1_of_allowed :
    step.outputs .cpuregs_rs1 =
      readRegister (step.inputs .decoded_rs1) (step.currentState .cpuregs) :=
  (cpuregsRs1Rule_holds_iff _ _ _).mp (allowed.1 .cpuregs_rs1)

/-- The second read port follows the same architectural register-zero rule. -/
theorem cpuregs_rs2_of_allowed :
    step.outputs .cpuregs_rs2 =
      readRegister (step.inputs .decoded_rs2) (step.currentState .cpuregs) :=
  (cpuregsRs2Rule_holds_iff _ _ _).mp (allowed.1 .cpuregs_rs2)

/-- The complete register array advances according to the write/reset rule in
`Regs.lean`. -/
theorem next_cpuregs_of_allowed :
    step.nextState .cpuregs =
      nextRegisters (step.inputs .resetn) (step.inputs .cpuregs_write)
        (step.inputs .latched_rd) (step.inputs .cpuregs_wrdata)
        (step.currentState .cpuregs) := by
  rw [allowed.2]
  rfl

end AllowedStep

/-- The authored register-file hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete register-file hierarchy have one
solution for each boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

end PicoRV.Regs
