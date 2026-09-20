import Silean.Authoring.CircuitArithmetic

namespace SileanTests.CircuitArithmetic

open Silean
open Silean.Authoring.CircuitDescription
open Silean.Authoring
open scoped Silean.Authoring

private noncomputable def addDescription := build do
  let left ← input "left" (.vector 2 .bit)
  let right ← input "right" (.vector 4 .bit)
  output "result" (← left +uu right)

-- Unequal inputs are zero-extended to max(2, 4) + 1 = 5 bits.
example : addDescription.outputs.map (fun output => output.port.signalType) =
    [.vector 5 .bit] := rfl

example : addDescription.children.map (fun child => child.name) =
    [.indexed "vector_layout" 0, .indexed "vector_layout" 1,
      .indexed "constant" 0, .indexed "add" 0] := rfl

private noncomputable def subtractDescription := build do
  let left ← input "left" (.vector 4 .bit)
  let right ← input "right" (.vector 2 .bit)
  output "result" (← left -ss right)

example : subtractDescription.outputs.map (fun output => output.port.signalType) =
    [.vector 5 .bit] := rfl

example : subtractDescription.children.map (fun child => child.name) =
    [.indexed "vector_layout" 0, .indexed "vector_layout" 1,
      .indexed "constant" 0, .indexed "add_sub" 0] := rfl

private noncomputable def allOperatorsDescription := build do
  let left ← input "left" (.vector 2 .bit)
  let right ← input "right" (.vector 4 .bit)
  output "add_uu" (← left +uu right)
  output "add_us" (← left +us right)
  output "add_su" (← left +su right)
  output "add_ss" (← left +ss right)
  output "subtract_uu" (← left -uu right)
  output "subtract_us" (← left -us right)
  output "subtract_su" (← left -su right)
  output "subtract_ss" (← left -ss right)

-- Every signedness combination has the same max-input-width-plus-one shape.
example : allOperatorsDescription.outputs.all fun output =>
    output.port.signalType = .vector 5 .bit := by decide

private noncomputable def allTruncatingOperatorsDescription := build do
  let left ← input "left" (.vector 2 .bit)
  let right ← input "right" (.vector 4 .bit)
  output "add_uu" (← left +uut right)
  output "add_us" (← left +ust right)
  output "add_su" (← left +sut right)
  output "add_ss" (← left +sst right)
  output "subtract_uu" (← left -uut right)
  output "subtract_us" (← left -ust right)
  output "subtract_su" (← left -sut right)
  output "subtract_ss" (← left -sst right)

-- A trailing `t` retains the larger input width instead of adding one bit.
example : allTruncatingOperatorsDescription.outputs.all fun output =>
    output.port.signalType = .vector 4 .bit := by decide

private noncomputable def equalWidthTruncatingDescription := build do
  let left ← input "left" (.vector 4 .bit)
  let right ← input "right" (.vector 4 .bit)
  output "result" (← left +uut right)

-- Equal-width truncation does not place redundant identity layouts.
example : equalWidthTruncatingDescription.children.map (fun child => child.name) =
    [.indexed "constant" 0, .indexed "add" 0] := rfl

def twoBits : Fin 2 → Bool
  | 0 => false
  | 1 => true

-- Unsigned extension fills high bits with zero; signed extension copies bit 1.
#guard !(Modules.VectorLayout.apply (extendLayout false 2 4) twoBits 3)
#guard Modules.VectorLayout.apply (extendLayout true 2 4) twoBits 3

end SileanTests.CircuitArithmetic
