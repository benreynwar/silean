import Silean.Authoring.CircuitLogic
import Silean.Modules.Mux.MuxTheorems

namespace SileanTests.CircuitLogic

open Silean
open Silean.Authoring.CircuitDescription
open scoped Silean.Authoring.CircuitLogic

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

namespace SileanTests.CircuitLogic.MuxCorrespondence

open Silean Naming Authoring.CircuitDescription

example (signalType : SignalType)
    {step : (Modules.Mux.cycleContract signalType).Step}
    (allowed : (Modules.Mux.cycleContract signalType).Allows step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Modules.Mux.result_of_allowed signalType allowed

example (signalType : SignalType)
    {step : (Modules.Mux.moduleStructure signalType).Step}
    (realizes : (Modules.Mux.moduleStructure signalType).Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Modules.Mux.Description.result_of_realization signalType realizes

example (signalType : SignalType) :
    Contracts.Cycle.Implements
      (Modules.Mux.moduleStructure signalType)
      (Modules.Mux.cycleContract signalType)
      (Modules.Mux.certification signalType).stateCorresponds :=
  Modules.Mux.implements_contract signalType

-- Correspondence checks actual wiring, not merely matching interfaces.
example (signalType : SignalType) :
    some { Modules.Mux.Description.description signalType with outputs :=
      [⟨⟨"result", signalType⟩, .input "whenTrue"⟩] } ≠
        ofNaming (Modules.Mux.naming signalType) := by
  intro assumed
  have equal := assumed.trans
    (Modules.Mux.Description.authored_definition_corresponds signalType).same.symm
  have sources := congrArg (fun value : Option Description =>
    value.map fun circuit => circuit.outputs.map (·.source)) equal
  change some [Source.input "whenTrue"] =
    some [Source.child (.indexed "bitwise_or" 0) _] at sources
  cases sources

-- Name uniqueness is a checked obligation, not an assumption of the builder.
example (signalType : SignalType) :
    ¬ ({ Modules.Mux.Description.description signalType with inputs :=
      [⟨"select", .bit⟩, ⟨"select", .bit⟩] } : Description).UniqueNames := by
  intro names
  have distinct := names.1
  change ([SourceName.plain "select", SourceName.plain "select"] ++ _).Nodup at distinct
  simp at distinct

end SileanTests.CircuitLogic.MuxCorrespondence

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
    { inputs := [{ name := "source", signalType := .bit }]
      outputs := [⟨⟨"result", .bit⟩, .input "source"⟩]
      namedWires := [⟨"result", .bit, .input "source"⟩] } := by
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
    { inputs := [{ name := "source", signalType := .bit }]
      outputs := [⟨⟨"result", .bit⟩, .input "source"⟩]
      namedWires := [⟨"first", .bit, .input "source"⟩,
        ⟨"second", .bit, .input "source"⟩] } := by
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
open scoped Silean.Authoring.CircuitLogic

private noncomputable def immediateWire := buildResult do
  let source ← input "source" .bit
  wire inverted ← !! source
  output "result" inverted

-- The inferred form binds the net and records the binder spelling against its
-- resolved source without inserting another child or structural endpoint.
example : immediateWire = .ok
    { inputs := [{ name := "source", signalType := .bit }]
      outputs := [⟨⟨"result", .bit⟩, .child (.indexed "not" 0) "out"⟩]
      children := [{
        name := .indexed "not" 0
        module := Silean.Primitives.notDesign
        inputs := [⟨⟨"in", .bit⟩, .input "source"⟩] }]
      namedWires := [⟨"inverted", .bit, .child (.indexed "not" 0) "out"⟩] } := by
  rfl

-- The annotated immediate form checks the declared signal type.
example : (buildResult do
    let source ← input "source" .bit
    wire observed : .bit ← pure source
    output "result" observed) = .ok
      { inputs := [⟨"source", .bit⟩]
        outputs := [⟨⟨"result", .bit⟩, .input "source"⟩]
        namedWires := [⟨"observed", .bit, .input "source"⟩] } := by
  rfl

-- Duplicate wire names are rejected across immediate declarations.
example : (buildResult do
    let source ← input "source" .bit
    wire observed ← pure source
    wire observed ← pure observed
    output "result" observed) = .error .duplicateWireName := by
  rfl

end SileanTests.CircuitLogic.ImmediateWires
