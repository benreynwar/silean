import Silean.FIRRTL
import Silean.Naming.PrimitiveNaming
import Silean.Modules.BitMux.BitMux
import Silean.Modules.FullAdder.FullAdder
import Silean.Modules.Register.Register
import Silean.Modules.Mux.Mux
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Modules.TupleField.TupleField
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.OneEntryFifo.OneEntryFifo
import Silean.Authoring.ModuleDesign
import Silean.Authoring.SignalSchemaDeclaration
import Silean.Emitters.StructuredPayload

namespace Silean.Examples.Checks.FIRRTL

open Silean Silean.FIRRTL
open Silean.Authoring

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

private def excludesAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all fun fragment => !(contains text fragment)

#guard containsAll (renderCircuit Modules.BitMux.naming)
  ["circuit BitMux", "public module BitMux",
   "inst chooseFalse of and_bit", "connect combine.left, chooseFalse.out"]

#guard containsAll (renderCircuit Modules.FullAdder.naming)
  ["circuit FullAdder", "public module FullAdder",
   "inst operands of HalfAdder", "inst carry of HalfAdder",
   "inst combineCarry of or_bit", "connect carry.left, operands.sum",
   "connect carryOut, combineCarry.out"]

private def opaqueNotNaming :
    Naming.ModuleNaming (.blackbox Primitives.not) :=
  .blackbox ⟨"opaque", "not", []⟩ Naming.Primitive.unaryPorts
    Naming.Primitive.emptySignals

#guard containsAll (renderCircuit opaqueNotNaming)
  ["circuit opaque_not", "extmodule opaque_not", "input clock : Clock",
   "input in : UInt<1>", "output out : UInt<1>"]

#guard containsAll (renderCircuit (Modules.Register.Naming.naming (.vector 2 .bit)))
  ["public module register_structural_v2_bit",
   "reg stored : UInt<1>, clock", "connect register_component_0.clock, clock",
   "connect aggregate_0[1], component_1"]

#guard containsAll (renderCircuit
  (Modules.EnabledRegister.naming (.tuple (.cons .bit (.cons .bit .nil)))))
  ["public module EnabledRegister_t_bit_bit_unit",
   "inst selection of Mux_t_bit_bit_unit",
   "connect storage.clock, clock", "{ _0 : UInt<1>, _1 : UInt<1> }"]

signal_schema NamedPair where
  valid : SignalSchema.bit,
  payload : SignalSchema.bit

signal_schema NestedPayload where
  tag : SignalSchema.bit,
  contents : NamedPair.schema

private abbrev namedPairType := NamedPair.signalType
private abbrev nestedPayloadType := NestedPayload.signalType
private abbrev pairVectorSchema := SignalSchema.vector 2 NamedPair.schema
private abbrev pairVectorType := SignalSchema.signalType pairVectorSchema

module_design DifferentlyNamedFlat where
  ports {
    input data (schema := NamedPair.schema) : namedPairType,
    output result (schema := NamedPair.schema) : namedPairType }
  instances {
    storage := Modules.Register.design namedPairType }
  wiring {
    outputs { .result := storage.output }
    instance (.storage) { .input := input.data }
  }

module_design DifferentlyNamedNested where
  ports {
    input data (schema := NestedPayload.schema) : nestedPayloadType,
    output result (schema := NestedPayload.schema) : nestedPayloadType }
  instances {
    storage := Modules.Register.design nestedPayloadType }
  wiring {
    outputs { .result := storage.output }
    instance (.storage) { .input := input.data }
  }

module_design DifferentlyNamedVectorElements where
  ports {
    input data (schema := pairVectorSchema) : pairVectorType,
    output result (schema := pairVectorSchema) : pairVectorType }
  instances {
    storage := Modules.Register.design pairVectorType }
  wiring {
    outputs { .result := storage.output }
    instance (.storage) { .input := input.data }
  }

module_design SameNamedAggregate where
  ports {
    input data (schema := NestedPayload.schema) : nestedPayloadType,
    output result (schema := NestedPayload.schema) : nestedPayloadType }
  instances {
    storage := Modules.Register.designWith
      NestedPayload.schema }
  wiring {
    outputs { .result := storage.output }
    instance (.storage) { .input := input.data }
  }

#guard containsAll (renderRootModule DifferentlyNamedFlat.naming)
  ["connect storage.in._0, data.valid",
   "connect storage.in._1, data.payload",
   "connect result.valid, storage.out._0",
   "connect result.payload, storage.out._1"]
#guard excludesAll (renderRootModule DifferentlyNamedFlat.naming)
  ["connect storage.in, data", "connect result, storage.out"]

#guard containsAll (renderRootModule DifferentlyNamedNested.naming)
  ["connect storage.in._0, data.tag",
   "connect storage.in._1._0, data.contents.valid",
   "connect storage.in._1._1, data.contents.payload",
   "connect result.contents.valid, storage.out._1._0"]
#guard excludesAll (renderRootModule DifferentlyNamedNested.naming)
  ["connect storage.in, data", "connect result, storage.out"]

#guard containsAll (renderRootModule DifferentlyNamedVectorElements.naming)
  ["connect storage.in[0]._0, data[0].valid",
   "connect storage.in[0]._1, data[0].payload",
   "connect result[1].valid, storage.out[1]._0",
   "connect result[1].payload, storage.out[1]._1"]
#guard excludesAll (renderRootModule DifferentlyNamedVectorElements.naming)
  ["connect storage.in, data", "connect result, storage.out"]

#guard containsAll (renderRootModule SameNamedAggregate.naming)
  ["connect storage.in, data", "connect result, storage.out"]

-- A named mux boundary may feed the canonical positional hierarchy used by
-- its generic implementation, including nested aggregates and vectors of
-- aggregates.
#guard containsAll (renderCircuit
  (Modules.Mux.namingWith namedPairType NamedPair.schema))
  ["input whenFalse : { valid : UInt<1>, payload : UInt<1> }",
   "output result : { valid : UInt<1>, payload : UInt<1> }",
   "inst chooseFalse of mask_structural_t_bit_bit_unit"]

#guard containsAll (renderCircuit
  (Modules.Mux.namingWith nestedPayloadType NestedPayload.schema))
  ["input whenTrue : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "inst combine of bitwise_or_structural_t_bit_t_bit_bit_unit_unit"]

#guard containsAll (renderCircuit
  (Modules.Mux.namingWith pairVectorType pairVectorSchema))
  ["input whenFalse : { valid : UInt<1>, payload : UInt<1> }[2]",
   "output result : { valid : UInt<1>, payload : UInt<1> }[2]"]

#guard containsAll (renderCircuit
  (Modules.EnabledRegister.namingWith namedPairType NamedPair.schema))
  ["{ valid : UInt<1>, payload : UInt<1> }",
   "input data : { valid : UInt<1>, payload : UInt<1> }",
   "output q : { valid : UInt<1>, payload : UInt<1> }"]

-- Custom field names stay on the authored register-bank boundary and are
-- propagated recursively for emission without changing its canonical
-- structure or certification.
#guard containsAll (renderCircuit
  (Modules.RegisterBank.Naming.namingWith nestedPayloadType 1 1
    NestedPayload.schema))
  ["input write_value : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "output read_0_value : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "input data : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "output q : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }"]

#guard containsAll (renderCircuit
  (Modules.TupleField.designWith NamedPair.signalMap .payload NamedPair.schema).naming)
  ["input tuple : { valid : UInt<1>, payload : UInt<1> }",
   "connect field, split.payload"]

-- Named authored boundaries are thin wrappers around canonical positional
-- tuple adapters, including recursively named aggregate fields.
#guard containsAll (renderCircuit
  (Modules.NamedTupleCombiner.designWith
    NestedPayload.signalMap NestedPayload.schema).naming)
  ["input tag : UInt<1>",
   "input contents : { valid : UInt<1>, payload : UInt<1> }",
   "output value : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "inst adapter of combine_aggregate_t_bit_t_bit_bit_unit_unit"]

#guard containsAll (renderCircuit
  (Modules.NamedTupleSplitter.designWith
    NestedPayload.signalMap NestedPayload.schema).naming)
  ["input value : { tag : UInt<1>, contents : { valid : UInt<1>, payload : UInt<1> } }",
   "output tag : UInt<1>",
   "output contents : { valid : UInt<1>, payload : UInt<1> }",
   "inst adapter of split_aggregate_t_bit_t_bit_bit_unit_unit"]

#guard containsAll (renderCircuit (Modules.OneEntryFifo.naming (.vector 2 .bit)))
  ["public module OneEntryFifo_v2_bit",
   "inst validStorage of EnabledResetRegister_bit_0",
   "inst dataStorage of EnabledRegister_v2_bit",
   "connect validStorage.reset, reset",
   "connect dataStorage.clock, clock", "reg stored : UInt<1>, clock"]

#guard containsAll (renderCircuit
  (Modules.OneEntryFifo.namingWith
    Silean.Emitters.StructuredPayload.type
    Silean.Emitters.StructuredPayload.naming))
  ["{ a : UInt<1>[3], b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] } }",
   "connect output_data.a, outputDataMux.result._0",
   "connect dataStorage.data._1._0, input_data.b.c",
   "connect outputDataMux.whenFalse._1._1[1]._0, input_data.b.d[1].e",
   "connect outputDataMux.whenTrue, dataStorage.q"]

end Silean.Examples.Checks.FIRRTL
