import Silean.Authoring.CircuitLogic
import Silean.Modules.Mux.MuxDerived

namespace SileanTests.CircuitLogic

open Silean
open Silean.Authoring.CircuitDescription
open scoped Silean.Authoring

private noncomputable def bitAndDescription := build do
  let left ← input "left" .bit
  let right ← input "right" .bit
  output "result" (← left &&& right)

-- Two bits place the primitive AND gate, rather than Mask or BitwiseAnd.
example : bitAndDescription.children.map (fun child => child.name) =
    [.indexed "and" 0] := rfl

private noncomputable def bitXorDescription := build do
  let left ← input "left" .bit
  let right ← input "right" .bit
  output "result" (← left ^^^ right)

-- Two bits place the primitive XOR gate.
example : bitXorDescription.children.map (fun child => child.name) =
    [.indexed "xor" 0] := rfl

private abbrev wordType : SignalType := .vector 4 .bit

private noncomputable def maskDescription := build do
  let value ← input "value" wordType
  let enabled ← input "enabled" .bit
  output "result" (← value &&& enabled)

-- An aggregate value and one bit place Mask.
example : maskDescription.children.map (fun child => child.name) =
    [.indexed "mask" 0] := rfl

private noncomputable def bitwiseAndDescription := build do
  let left ← input "left" wordType
  let right ← input "right" wordType
  output "result" (← left &&& right)

-- Equally typed aggregate values place BitwiseAnd.
example : bitwiseAndDescription.children.map (fun child => child.name) =
    [.indexed "bitwise_and" 0] := rfl

private noncomputable def bitwiseXorDescription := build do
  let left ← input "left" wordType
  let right ← input "right" wordType
  output "result" (← left ^^^ right)

-- Equally typed aggregate values place BitwiseXor.
example : bitwiseXorDescription.children.map (fun child => child.name) =
    [.indexed "bitwise_xor" 0] := rfl

private noncomputable def notOrDescription := build do
  let left ← input "left" .bit
  let right ← input "right" .bit
  let inverted ← !! left
  output "result" (← inverted ||| right)

-- On bits, the other two operators place primitive Not and OR gates.
example : notOrDescription.children.map (fun child => child.name) =
    [.indexed "not" 0, .indexed "or" 0] := rfl

end SileanTests.CircuitLogic

namespace SileanTests.CircuitLogic.Mux

open Silean Naming Authoring.CircuitDescription

example (signalType : SignalType)
    {step : (Modules.Mux.cycleContract signalType).Step}
    (allowed : (Modules.Mux.cycleContract signalType).Allows step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Modules.Mux.cycleContract.result signalType allowed

example (signalType : SignalType)
    {step : (Modules.Mux.moduleStructure signalType).Step}
    (realizes : (Modules.Mux.moduleStructure signalType).Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Modules.Mux.result_of_realization signalType realizes

example (signalType : SignalType) :
    Contracts.Cycle.Implements
      (Modules.Mux.moduleStructure signalType)
      (Modules.Mux.cycleContract signalType)
      (Modules.Mux.certification signalType).stateCorresponds :=
  Modules.Mux.implements_contract signalType

example (signalType : SignalType) :
    (Modules.Mux.description signalType).ImplementsCycleContract
      (Modules.Mux.cycleContract signalType)
      (Modules.Mux.Naming.ports signalType) :=
  Modules.Mux.construction_correct signalType

private def duplicateNames := buildResult do
  let first ← input "same" .bit
  let second ← input "same" .bit
  output "same" first
  output "same" second

-- Names are metadata: duplicate spellings do not merge structural endpoints.
example : duplicateNames = .ok
    { inputs := [
        { id := ⟨0⟩, name := "same", signalType := .bit },
        { id := ⟨1⟩, name := "same", signalType := .bit }]
      outputs := [
        ⟨{ id := ⟨0⟩, name := "same", signalType := .bit }, .input ⟨0⟩⟩,
        ⟨{ id := ⟨1⟩, name := "same", signalType := .bit }, .input ⟨1⟩⟩] } := by
  rfl

end SileanTests.CircuitLogic.Mux

namespace SileanTests.CircuitLogic.Wires

open Silean
open Silean.Authoring.CircuitDescription

/-! These examples exercise forward-declared wires. A successful build retains
their names but contains only resolved `Source` values; invalid drafts retain a
precise error through `buildResult`. -/

private def directWire := buildResult do
  let source <- input "source" .bit
  wire result : .bit
  assign result source
  output "result" result

-- A forward-declared wire resolves to its unique source and retains its name.
example : directWire = .ok
    { inputs := [{ id := ⟨0⟩, name := "source", signalType := .bit }]
      outputs := [⟨⟨⟨0⟩, "result", .bit⟩, .input ⟨0⟩⟩]
      namedWires := [⟨"result", .bit, .input ⟨0⟩⟩] } := by
  rfl

private def wireChain := buildResult do
  let source <- input "source" .bit
  wire first : .bit
  wire second : .bit
  assign first source
  assign second first
  output "result" second

-- Wire chains resolve transitively while retaining each declared name.
example : wireChain = .ok
    { inputs := [{ id := ⟨0⟩, name := "source", signalType := .bit }]
      outputs := [⟨⟨⟨0⟩, "result", .bit⟩, .input ⟨0⟩⟩]
      namedWires := [⟨"first", .bit, .input ⟨0⟩⟩,
        ⟨"second", .bit, .input ⟨0⟩⟩] } := by
  rfl

-- Every declared wire must have exactly one driver, even if it is unused.
example : (buildResult do
    wire missing : .bit
    output "result" missing) = .error (.undrivenWire "missing") := by
  rfl

example : (buildResult do
    let source <- input "source" .bit
    wire result : .bit
    assign result source
    assign result source) = .error (.multiplyDrivenWire "result") := by
  rfl

example : (buildResult do
    let _ ← Silean.Authoring.CircuitDescription.wire "same" .bit
    wire same : .bit
    output "result" same) = .error .duplicateWireName := by
  rfl

-- A cycle made only from wire aliases has no structural source to resolve to.
example : (buildResult do
    wire first : .bit
    wire second : .bit
    assign first second
    assign second first
    output "result" first) = .error .wireAliasCycle := by
  rfl

-- Inputs and child outputs are sources, not legal assignment destinations.
example : (buildResult do
    let source <- input "source" .bit
    assign source source) = .error .assignmentTargetNotWire := by
  rfl

end SileanTests.CircuitLogic.Wires

namespace SileanTests.CircuitLogic.ImmediateWires

open Silean
open Silean.Authoring.CircuitDescription
open scoped Silean.Authoring

private noncomputable def immediateWire := buildResult do
  let source ← input "source" .bit
  wire inverted ← !! source
  output "result" inverted

-- The inferred form binds the net and records the binder spelling against its
-- resolved source without inserting another child or structural endpoint.
example : immediateWire = .ok
    { inputs := [{ id := ⟨0⟩, name := "source", signalType := .bit }]
      outputs := [⟨⟨⟨0⟩, "result", .bit⟩, .child ⟨0⟩ ⟨0⟩⟩]
      children := [{
        id := ⟨0⟩
        name := .indexed "not" 0
        module := Silean.Primitives.notDesign
        inputs := [⟨⟨⟨0⟩, "in", .bit⟩, .input ⟨0⟩⟩] }]
      namedWires := [⟨"inverted", .bit, .child ⟨0⟩ ⟨0⟩⟩] } := by
  rfl

-- The annotated immediate form checks the declared signal type.
example : (buildResult do
    let source ← input "source" .bit
    wire observed : .bit ← pure source
    output "result" observed) = .ok
      { inputs := [⟨⟨0⟩, "source", .bit⟩]
        outputs := [⟨⟨⟨0⟩, "result", .bit⟩, .input ⟨0⟩⟩]
        namedWires := [⟨"observed", .bit, .input ⟨0⟩⟩] } := by
  rfl

-- Duplicate wire names are rejected across immediate declarations.
example : (buildResult do
    let source ← input "source" .bit
    wire observed ← pure source
    wire observed ← pure observed
    output "result" observed) = .error .duplicateWireName := by
  rfl

end SileanTests.CircuitLogic.ImmediateWires
