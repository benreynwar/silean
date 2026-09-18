import Silean.Examples.PicoRV.Decoder.Internal.DecoderInstructionSummaryVerification

/-! # Instruction-summary theorems

This is the supported proof interface for the instruction summary network.
Its reduction trees and structural certification remain under `Internal/`.
-/

namespace Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure

open Silean

/-- Every allowed step produces exactly the named instruction summaries. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  funext output
  cases output with
  | instr_trap =>
      exact (trapOutputRule_holds_iff _ _ _).mp
        (allowed.1 .trap)
  | is_lui_auipc_jal =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_lui_auipc_jal (by simp)
  | is_lui_auipc_jal_jalr_addi_add_sub =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_lui_auipc_jal_jalr_addi_add_sub (by simp)
  | is_slti_blt_slt =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_slti_blt_slt (by simp)
  | is_sltiu_bltu_sltu =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_sltiu_bltu_sltu (by simp)
  | is_lbu_lhu_lw =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_lbu_lhu_lw (by simp)
  | is_compare =>
      exact (summariesOutputRule_holds_iff _ _ _).mp
        (allowed.1 .summaries) .is_compare (by simp)

/-- Every realized structural step has the public summary behavior. -/
theorem outputs_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure
