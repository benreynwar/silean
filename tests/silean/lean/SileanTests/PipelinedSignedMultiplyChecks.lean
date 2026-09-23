import Silean.FIRRTL
import Silean.Modules.PipelinedSignedMultiply.PipelinedSignedMultiplyDerived

namespace SileanTests.PipelinedSignedMultiply

open Silean Silean.FIRRTL
open Silean.Modules.PipelinedSignedMultiply

def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputValues (leftWidth rightWidth : Nat) (left right : Int) :
    (ports leftWidth rightWidth).inputs.Values
  | .left => signedBits leftWidth left
  | .right => signedBits rightWidth right

example (leftWidth rightWidth latency : Nat) :
    ModuleStructuralCertification
      (moduleStructure leftWidth rightWidth latency) :=
  structuralCertification leftWidth rightWidth latency

example (leftWidth rightWidth latency : Nat)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth latency).State}
    {inputs : List (ports leftWidth rightWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth).outputs.Values}
    (execution : (moduleStructure leftWidth rightWidth latency).Executes
      initialState inputs outputs finalState) :
    contract leftWidth rightWidth latency execution.toBoundaryTrace :=
  contract_of_execution leftWidth rightWidth latency execution

#check place

-- Latency zero is the combinational signed multiplier.
example (initialState : (moduleStructure 4 3 0).State) :
    ∃ outputs finalState,
      (moduleStructure 4 3 0).Executes initialState
        [inputValues 4 3 (-3) 2] outputs finalState ∧
      ∃ outputInTrace : 0 < outputs.length,
        (BitVector.toBitVec 7
          (outputs.get ⟨0, outputInTrace⟩ .result)).toInt = -6 := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 4 3 0).hasSolution.execution_exists initialState
      [inputValues 4 3 (-3) 2]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 0 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  calc
    (BitVector.toBitVec 7
        (outputs.get ⟨0, outputInTrace⟩ .result)).toInt =
        (BitVector.toBitVec 4
          (([inputValues 4 3 (-3) 2].get ⟨0, by simp⟩) .left)).toInt *
        (BitVector.toBitVec 3
          (([inputValues 4 3 (-3) 2].get ⟨0, by simp⟩) .right)).toInt :=
      result_toInt_of_execution 4 3 0 execution 0 (by simp) outputInTrace
    _ = -6 := by native_decide

-- One register moves the first product to trace position one.
example (initialState : (moduleStructure 4 3 1).State) :
    ∃ outputs finalState,
      (moduleStructure 4 3 1).Executes initialState
        [inputValues 4 3 (-8) 3, inputValues 4 3 1 1]
        outputs finalState ∧
      ∃ outputInTrace : 1 < outputs.length,
        (BitVector.toBitVec 7
          (outputs.get ⟨1, outputInTrace⟩ .result)).toInt = -24 := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 4 3 1).hasSolution.execution_exists initialState
      [inputValues 4 3 (-8) 3, inputValues 4 3 1 1]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 1 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  calc
    (BitVector.toBitVec 7
        (outputs.get ⟨1, outputInTrace⟩ .result)).toInt =
        (BitVector.toBitVec 4
          (([inputValues 4 3 (-8) 3, inputValues 4 3 1 1].get
            ⟨0, by simp⟩) .left)).toInt *
        (BitVector.toBitVec 3
          (([inputValues 4 3 (-8) 3, inputValues 4 3 1 1].get
            ⟨0, by simp⟩) .right)).toInt :=
      result_toInt_of_execution 4 3 1 execution 0 (by simp) outputInTrace
    _ = -24 := by native_decide

-- A later input remains aligned through a multi-register chain.
example (initialState : (moduleStructure 3 5 3).State) :
    ∃ outputs finalState,
      (moduleStructure 3 5 3).Executes initialState
        [inputValues 3 5 1 1, inputValues 3 5 3 (-7),
          inputValues 3 5 2 2, inputValues 3 5 0 0,
          inputValues 3 5 (-1) 4]
        outputs finalState ∧
      ∃ outputInTrace : 4 < outputs.length,
        (BitVector.toBitVec 8
          (outputs.get ⟨4, outputInTrace⟩ .result)).toInt = -21 := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 3 5 3).hasSolution.execution_exists initialState
      [inputValues 3 5 1 1, inputValues 3 5 3 (-7),
        inputValues 3 5 2 2, inputValues 3 5 0 0,
        inputValues 3 5 (-1) 4]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 4 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  calc
    (BitVector.toBitVec 8
        (outputs.get ⟨4, outputInTrace⟩ .result)).toInt =
        (BitVector.toBitVec 3
          (([inputValues 3 5 1 1, inputValues 3 5 3 (-7),
              inputValues 3 5 2 2, inputValues 3 5 0 0,
              inputValues 3 5 (-1) 4].get ⟨1, by simp⟩) .left)).toInt *
        (BitVector.toBitVec 5
          (([inputValues 3 5 1 1, inputValues 3 5 3 (-7),
              inputValues 3 5 2 2, inputValues 3 5 0 0,
              inputValues 3 5 (-1) 4].get ⟨1, by simp⟩) .right)).toInt :=
      result_toInt_of_execution 3 5 3 execution 1 (by simp) outputInTrace
    _ = -21 := by native_decide

-- A zero-width operand still propagates the exact zero product through the
-- requested latency.
example (initialState : (moduleStructure 0 4 2).State) :
    ∃ outputs finalState,
      (moduleStructure 0 4 2).Executes initialState
        [inputValues 0 4 0 (-7), inputValues 0 4 0 3,
          inputValues 0 4 0 1]
        outputs finalState ∧
      ∃ outputInTrace : 2 < outputs.length,
        (BitVector.toBitVec 4
          (outputs.get ⟨2, outputInTrace⟩ .result)).toInt = 0 := by
  obtain ⟨outputs, finalState, execution⟩ :=
    (structuralCertification 0 4 2).hasSolution.execution_exists initialState
      [inputValues 0 4 0 (-7), inputValues 0 4 0 3,
        inputValues 0 4 0 1]
  have outputLength := ModuleStructure.Executes.length_eq execution
  have outputInTrace : 2 < outputs.length := by
    simp at outputLength
    omega
  refine ⟨outputs, finalState, execution, outputInTrace, ?_⟩
  calc
    (BitVector.toBitVec 4
        (outputs.get ⟨2, outputInTrace⟩ .result)).toInt =
        (BitVector.toBitVec 0
          (([inputValues 0 4 0 (-7), inputValues 0 4 0 3,
              inputValues 0 4 0 1].get ⟨0, by simp⟩) .left)).toInt *
        (BitVector.toBitVec 4
          (([inputValues 0 4 0 (-7), inputValues 0 4 0 3,
              inputValues 0 4 0 1].get ⟨0, by simp⟩) .right)).toInt :=
      result_toInt_of_execution 0 4 2 execution 0 (by simp) outputInTrace
    _ = 0 := by native_decide

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (leftWidth rightWidth latency : Nat) : Bool :=
  match renderRootModule (naming leftWidth rightWidth latency) with
  | .error _ => false
  | .ok text =>
      occurrences text "inst signed_multiply_" == 1 &&
      occurrences text "inst register_" == latency

#guard rootHasShape 4 3 0
#guard rootHasShape 4 3 1
#guard rootHasShape 3 5 3

#guard match renderRootModule (naming 4 3 0) with
  | .error _ => false
  | .ok text => contains text "public module PipelinedSignedMultiply_4_3_0" &&
      contains text "connect result, signed_multiply_0.result"

#guard match renderRootModule (naming 4 3 3) with
  | .error _ => false
  | .ok text => contains text "public module PipelinedSignedMultiply_4_3_3" &&
      contains text "connect register_0.in, signed_multiply_0.result" &&
      contains text "connect register_1.in, register_0.out" &&
      contains text "connect register_2.in, register_1.out" &&
      contains text "connect result, register_2.out"

#guard match renderCircuit (naming 4 3 3) with
  | .error _ => false
  | .ok text => contains text "public module PipelinedSignedMultiply_4_3_3" &&
      contains text "module SignedMultiply_4_3" &&
      contains text "module register_structural_v7_bit" &&
      contains text "module FullAdder"

end SileanTests.PipelinedSignedMultiply
