# Silean 2 roadmap

This roadmap records the current destination and remaining work. The current
design is described in `docs/Architecture.md`; source ownership is summarized
in `docs/SourceMap.md`.

## Direction

Silean 2 represents hardware as a typed recursive hierarchy with total wiring
and primitive storage. Its meaning is the order-independent
`ModuleStructure.IsSolution` relation. Independently declared cycle contracts
describe observable behavior, and certification proves that every structural
solution implements its contract. Module certificates supply structural
existence; certified schedules establish uniqueness.

The same computable hierarchy is consumed directly by naming and FIRRTL
generation. We do not lower to a second semantic netlist, and backend
translation is not part of the correctness proof at this stage.

## Established foundation

- Bits, vectors, and heterogeneous tuples have typed values and stable finite
  labels.
- Module ports contain connectivity only; structural state is derived from
  primitive storage and recursive child ownership.
- Instances, endpoints, and total typed wiring describe composite structure.
- Structural equations have an evaluation-order-independent meaning.
- Cycle contracts own independent abstract state, rule-local output
  dependencies, and an explicit-input next-state rule.
- Certified child rules and output/state schedules establish hierarchical
  availability and structural uniqueness without becoming circuit semantics.
- `ModuleCycleCertified` packages a computable structure, cycle contract, state
  correspondence, refinement proof, and structural existence/uniqueness.
- Generic Constant, balanced Reduction, All, recursive Equality, VectorConcat,
  BinaryToOneHot, CombMuxTree, RegisterBank, Register, Mask, BitwiseOr, Mux,
  EnabledRegister,
  OneEntryFifo, serial FIFO composition, and arbitrary positive-depth FIFO
  validate the hierarchy.
- `LeafwiseComposition` provides the shared recursive/fixed-input
  split/component/combine hierarchy, proposal-existence construction, and
  component-family scheduling used by Constant, Register, Mask, and BitwiseOr.
- FIFO cycle behavior, execution, and derived properties are separate layers.
  The properties prove conservation, capacity, and ready propagation over
  contract execution.
- Module-owned naming feeds direct FIRRTL generation; FIRRTL is converted to
  SystemVerilog and exercised with Verilator and cocotb.

## Working constraints

- Keep structure, contracts, proof schedules, naming, and backend rendering in
  separate ownership layers.
- Treat stateless modules as having zero-bit state, not as a separate kind.
- Prefer fully generic proof laws; do not add helpers specialized to one module
  merely to shorten a proof.
- Keep module structures computable and proof packages opaque when needed.
- Do not introduce lowering or raw numeric identities as semantic
  prerequisites.
- Keep focused Lean targets below five seconds.
- Do not use `sorry`, new axioms, `Classical.choice`, or `native_decide`.

## Completed repository cleanup

The repository-facing semantic-no-op cleanup established:

- one authoritative architecture document and one source map;
- aggregate imports reflecting directory ownership;
- removal of provisional APIs with no real consumer;
- separate test fixtures and regression checks; and
- verified Lean, FIRRTL conversion, and cocotb regressions.

## Completed leafwise composition review

Register, Mask, and BitwiseOr now share a generic aggregate hierarchy and one
generic structural-existence proof. Register validates recursive state, Mask
validates a broadcast bit beside one recursive input, and BitwiseOr validates
two recursive inputs. Their schedules retain the contract-specific dependency
facts, while their state-correspondence and refinement proofs retain the actual
operation semantics. The retention boundary and comparison are recorded in
`docs/LeafwiseComposition.md`.

## Completed FIFO organization review

FIFO organization is consolidated around the shared interface, cycle behavior,
one-entry storage, serial composition, positive depth, execution, and derived
properties. Module structures remain free of execution data; proof-construction
schedules and witnesses are private. The resulting organization and its
retention decisions are recorded in `docs/FifoOrganization.md`.

## Completed constant generation

A Boolean constant primitive and certified generic `Constant T value` module
now generate arbitrary bit, vector, and tuple values. Aggregate constants use
the leafwise component/combiner hierarchy with empty input families and
value-dependent recursive leaves. Naming keys include the flattened value, and
direct FIRRTL checks cover primitive and nested aggregate constants. This is
the first dependency for generic equality-with-constant and pointer logic.

## Completed balanced Boolean reduction

`Reduction` constructs and certifies a balanced hierarchy over any finite
family of same-typed inputs from a certified binary operation and certified
identity source. Empty families instantiate the identity, singleton families
are direct wires, and internal nodes recursively reduce two nearly equal
halves before applying the binary child. The tree construction proves both its
leaf count and recursive balance; generic schedules prove structural
uniqueness in left/right/combine order.

`All` instantiates that machinery with bit AND and constant true. Its public
contract deliberately does not expose tree parenthesization: it uses the
ordinary Lean recursion `every` and states that the result is true exactly
when every indexed input is true. A private certification bridge proves the
balanced structural reduction implements that natural contract. Direct FIRRTL
checks cover empty, singleton, and five-input hierarchies without adding a
cocotb target.

## Completed recursive equality

`Equality T` has two `T` inputs and one bit result. Its natural contract uses
the generic recursive value function `SignalType.equal`; the public law states
that the result is true exactly when the two Lean values are equal. The bit
case wraps the closed equality primitive. Vector and tuple structures split
both inputs into immediate components, recursively instantiate Equality for
corresponding components, and feed the indexed family of result bits into
`All`. This preserves aggregate hierarchy and does not impose a global
flattening order. Certification covers structural existence, schedule-based
uniqueness, and refinement for empty and nonempty aggregates. Lean and direct
FIRRTL checks cover bits, empty tuples, vectors, and nested tuples.

## Completed generic vector concatenation

`VectorConcat T leftWidth rightWidth` joins two vectors of `T` without
flattening their elements. Its natural contract uses `Fin.addCases`: left
elements occupy the indices below `leftWidth`, and right elements occupy the
remaining indices. The structure uses one splitter for each input and one
combiner for the result. Certification proves existence, schedule-based
uniqueness, and refinement; public index laws expose both halves. Lean and
direct FIRRTL checks cover either empty half, two nonempty halves, and
aggregate element types.

## Completed binary-to-one-hot decoding

`BinaryToOneHot width` interprets its input bits most-significant first and
produces `2 ^ width` result bits. Its contract is numeric: output index `i` is
true exactly when `i` is the natural-number value of the input. The certified
structure is recursive rather than an equality bank. Width zero emits the
one-element constant `[true]`; each successor width splits off the leading
bit, reconstructs and decodes the tail, masks the decoded vector with the bit
and its inverse, and joins the two halves with `VectorConcat`. Public theorems
connect the numeric law to the recursive decoder. Lean and direct FIRRTL checks
cover widths zero through three; no cocotb target is needed for this module.

## Completed combinational mux tree

`CombMuxTree T indexWidth` takes `2 ^ indexWidth` values of type `T` and a
big-endian bit-vector index. Its natural contract returns the value at the
numeric index. The recursive structure partitions the values with the generic
certified `VectorSplit`, rebuilds the selector tail using ordinary signal
adapters, evaluates two smaller mux trees, and selects between their results
with `Mux T`. `VectorSplit` is the reusable inverse-shaped counterpart of
`VectorConcat`, rather than a mux-specific adapter. Certification proves
existence, schedule-based uniqueness, and refinement. Lean and direct FIRRTL
checks cover index widths zero through three and both bit and aggregate values.

## Completed generic register bank

`RegisterBank T addressWidth` contains `2 ^ addressWidth` entries with one
synchronous write port and one combinational read port. Its natural contract
stores a vector of `T`: reading returns the currently addressed pre-update
entry, while an enabled write replaces exactly one next-state entry and all
others remain unchanged. The structure decodes the write address with
`BinaryToOneHot`, gates the global write enable per entry, instantiates one
generic `EnabledRegister T` per entry, combines their outputs, and reads through
`CombMuxTree T`. The state correspondence relates the contract vector
pointwise to that register family. Certification proves structural existence,
schedule-based uniqueness, and refinement, and public laws expose read,
selected-write, and retention behavior. Lean checks, direct FIRRTL conversion,
and a four-entry cocotb test cover initialization, reads, writes, retention,
and same-address read-before-write behavior. The implementation uses a private
named child-instance type rather than nested sums, keeps construction witnesses
private, and shares `BitVector.toIndex` as the generic numeric interpretation
used by the decoder, mux tree, and register bank.

## Later work

1. Build the pointer and memory pieces needed for a practical FIFO backed by a
   register bank or later memory primitive, keeping its contract independent
   of the chosen storage hierarchy.
2. Review intentionally public module theorems and remove debugging or
   construction details that no consumer needs.
3. Expand direct FIRRTL emission to additional configured designs as useful;
   keep translation straightforward and executable rather than proof-heavy.
4. Add reset semantics only when a concrete module requires them.
5. Consider backend correctness or trace packaging only when a real consumer
   makes the additional proof layer valuable.

Each architectural goal ends with a plain-language review, focused timing,
full Lean verification, and relevant external simulation.
