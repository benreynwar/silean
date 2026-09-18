# Leafwise aggregate composition

Leafwise modules apply the same behavior independently to each bit contained
in a `SignalType`. Vectors and tuples therefore share one physical pattern:

1. split each recursively shaped input into its immediate components;
2. instantiate one recursively certified child per component;
3. broadcast any fixed-shape inputs directly to every child; and
4. combine each family of child outputs back into the aggregate shape.

`Composition.LeafwiseInterface` describes the public labels and classifies
inputs as recursive or fixed. It owns the generic instance enumeration, typed
wiring, recursive `ModuleStructure`, child-contract boundary, and finite-family
schedule constructor. Public module labels remain meaningful names rather than
being replaced by positional unary or binary interfaces.

Current users include:

| Module family | Recursive inputs | Fixed inputs | Outputs | Contract state |
| --- | --- | --- | --- | --- |
| Register | `input : T` | none | `output : T` | `stored : T` |
| Mask | `value : T` | `mask : bit` | `result : T` | none |
| Constant | none | none | `output : T` | none |
| BinaryLeafwise | `left : T`, `right : T` | none | `result : T` | none |

## Certified binary operations

`Composition.BinaryLeafwise` specializes the general hierarchy to stateless
binary operations. It contains the only bit wrapper, output/state schedules,
aggregate refinement proof, and recursive certification for this pattern.
`Naming.BinaryLeafwise` supplies the corresponding generic naming traversal
without reversing the dependency from structural composition into naming.

A concrete operation supplies two small descriptors:

- `BinaryLeafwise.Operation` gives the natural Lean function at every
  `SignalType` and proves that splitting an aggregate result agrees with
  applying it independently to the immediate components.
- `BinaryLeafwise.BitGate` supplies a certified two-input, one-output bit gate,
  identifies its public rule and dependencies, and connects that rule to the
  Lean bit operation.

`Modules.BitwiseAnd`, `Modules.BitwiseOr`, and `Modules.BitwiseXor` instantiate
those descriptors with their existing primitives. Their files retain only the
operation-specific public names, contract-facing laws, and naming metadata;
they do not contain recursive schedules or certification proofs.

## Meaning and proof boundary

The structural meaning remains the simultaneous equations of
`ModuleStructure`; neither `LeafwiseInterface` nor `BinaryLeafwise` introduces
an evaluator. Their schedules are proof witnesses used to establish existence
and uniqueness.

For a binary aggregate layer, the proof:

1. calls both input splitters;
2. calls the selected public rule of every recursively certified component;
3. calls the output combiner;
4. obtains child behavior only through each child certificate; and
5. uses `Operation.split_apply` plus the splitter/combiner inverse laws to
   prove the natural aggregate contract.

Register, Mask, and Constant keep their own semantic certification because
their state, broadcast inputs, or zero-input behavior are materially different.
They reuse the general leafwise hierarchy without being forced through the
binary-operation abstraction.
