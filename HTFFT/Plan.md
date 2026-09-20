# HTFFT port and verification plan

> **Status: highly provisional living document.**
>
> This plan records the current starting point, not a settled design. It is
> expected to change as the first arithmetic components are implemented, the
> proof boundaries become clearer, and generated hardware is inspected. In
> particular, names, hierarchy, contracts, parameterization, and milestone
> order may all evolve. Update this document when implementation experience
> invalidates an assumption rather than preserving an obsolete plan.

## Objective

Port the current `htfft` hardware design into Lean as a Silean client design.
The Silean structure will be the implementation under verification and the
source from which RTL is generated. The existing VHDL and Python generators
are design references and useful regression oracles; equivalence with that
source is not the primary formal theorem.

The intended end result has two principal guarantees:

1. the Silean hardware exactly implements a specified streaming fixed-point
   FFT algorithm; and
2. the decoded fixed-point result has a proved error bound relative to a
   mathematical discrete Fourier transform.

These are distinct claims. The first is an exact hardware-refinement result.
The second is an approximation result accounting for input quantization,
twiddle quantization, truncation, and any relevant range assumptions.

## Initial scope

The first implementation should retain the important characteristics of the
current design:

- radix-2 FFT sizes that are powers of two;
- a power-of-two number of samples consumed per cycle;
- packed signed fixed-point complex samples;
- an unrolled FFT over the samples consumed in one cycle;
- subsequent streaming stages backed by memories;
- configurable pipeline placement where it remains useful;
- growth by one bit per real and imaginary component at each butterfly stage;
- generated RTL suitable for synthesis and simulation.

The current design assumes consecutively presented packet data and primarily
tests back-to-back vectors. The first contract may state that environmental
assumption explicitly. Supporting gaps, backpressure, floating point, or
stage-specific precision trimming is outside the initial scope unless early
work shows that one of these must be designed in from the start.

## Proposed proof layers

The current working decomposition is:

```text
Silean structural circuit
        |
        | exact cycle and trace refinement
        v
streaming fixed-point FFT specification
        |
        | decoding and numerical error theorem
        v
mathematical complex DFT specification
```

The structural proof should not depend on complex analysis. It should establish
the exact Boolean, signed-integer, truncation, state, framing, and ordering
behavior of the circuit. Mathematical reasoning should occur against the pure
fixed-point specification exposed by that proof.

## Likely source organization

This is only a sketch. Files and boundaries should follow the proof rather than
being created in advance merely to match this list.

```text
HTFFT/
|- Plan.md
|- FixedPoint.lean
|- Twiddle.lean
|- Butterfly.lean
|- UnrolledFFT.lean
|- StreamingStage.lean
|- InitialMemory.lean
|- FinalMemory.lean
|- HTFFT.lean
|- Math/
|  |- DFT.lean
|  `- Error.lean
|- Internal/
|  |- ...Structure.lean
|  `- ...Verification.lean
`- Emitters/
   `- HTFFT.lean
```

Public files should expose natural contracts and useful theorems. Detailed
structure, schedules, and certification proofs can move under `Internal/` when
the appropriate boundaries are known.

## Phase 1: arithmetic foundations

Before building an FFT hierarchy, determine which reusable facilities Silean
needs for this design. The likely minimum is:

- two's-complement interpretation of bit vectors and associated bounds;
- sign extension and fixed-width slicing laws;
- full-width signed multiplication;
- exact fixed-point product truncation matching the intended hardware;
- a synthesis-friendly pipelined multiplier;
- a shift register or delay abstraction suitable for pipeline alignment; and
- a synchronous memory abstraction with explicit read/write collision
  behavior.

Reusable, design-independent components should live under `Silean/`; HTFFT
packing, scaling, and numerical conventions should remain under `HTFFT/`.

The initial multiplier will be a structural composition of smaller modules.
Memory still requires a separate decision about its primitive boundary.
Generated RTL quality, RAM inference, and the existing Silean proof boundary
should guide that choice.

### Initial structural multiplier decomposition

For the first implementation, multiplication will be a certified structural
composition terminating in low-level Boolean, register, and constant
primitives. Direct multiplication primitives may be added later for targets
such as FPGAs, while retaining the same public multiplication contract. Radix-4
Booth encoding is also deferred: the initial design will use ordinary binary
partial products so that the arithmetic and compressor proofs can be
established before introducing signed recoding and correction cases.

The tentative module stack is:

```text
PartialProductRow
        |
        v
CarrySaveAdder (three operands to two)
        |
        v
CarrySaveLayer (one parallel compression level)
        |
        v
CarrySaveTree
        |
        v
final full-width Add
        |
        v
UnsignedMultiply
        |
        v
ConditionalNegate wrappers
        |
        v
SignedMultiply
        |
        v
VectorDelay or registered compressor boundaries
        |
        v
PipelinedSignedMultiply
```

Current implementation status:

- [x] `VectorReindex`: generic pure-wiring reindexing for vectors of any
  signal type, implemented by exactly one splitter and one combiner, with a
  natural element-selection contract and structural certification.
- [x] `PartialProductRow`: natural numerical contract, authored low-level
  `Mask`/`VectorLayout` implementation, certification, and focused tests.
- [x] `CarrySaveAdder`: natural three-to-two contract, one indexed
  `FullAdder` per bit, fixed-width shifted carry, structural certification,
  modular-sum theorem, and zero-/one-/multi-bit RTL checks. It deliberately
  has no duplicate authored `ModuleBuilder` description; the indexed
  `module_design` is its sole hardware representation.
- [x] `CarrySaveLayer`: natural custom relational contract, indexed parallel
  compressors, a flat intermediate vector followed by `VectorReindex` into
  sum/carry interleaving, contract-independent structural certification,
  direct relational proof through the public `CarrySaveAdder` arithmetic
  theorem, closed hierarchy checks, and RTL compressor-count tests.
- [x] `CarrySaveTree`: natural collection-level relational contract, recursive
  `CarrySaveLayer` structure, exact zero-/one-/two-operand base cases, direct
  structural certification and preservation proof, closed hierarchy checks,
  and recursive RTL compressor-count tests. This successfully uses a custom
  contract without a duplicate deterministic `ModuleCycleContract`.
- [x] `UnsignedMultiply`: natural exact full-width product contract, one
  indexed `PartialProductRow` per multiplier bit, `CarrySaveTree` reduction,
  final `Add`, contract-independent structural certification, exact
  realization theorem, zero-/asymmetric-width coverage, closed hierarchy
  checks, and RTL-shape tests. The later signed and pipelined layers remain
  dependent on it.

The proposed responsibilities are:

- `PartialProductRow` gates the multiplicand with one multiplier bit and places
  the result at a fixed bit offset in a full product-width vector. It should be
  built from `Mask` and `VectorLayout`. Its numerical theorem states that the
  row denotes either zero or the multiplicand multiplied by the appropriate
  power of two.
- `CarrySaveAdder` compresses three equally wide operands into `sum` and
  shifted `carry` operands using one `FullAdder` per bit and no inter-bit carry
  propagation. Its contract states that the two outputs preserve the three
  input operands' sum modulo the vector width.
- `CarrySaveLayer` performs one parallel level of three-to-two compression and
  passes through the zero, one, or two operands left outside complete triples.
  It is public because it has its own useful boundary and semantic guarantee;
  its indexed compressors and grouping remain internal.
- `CarrySaveTree` publicly relates a collection of operands to two result
  operands by preservation of their total modulo the common width. Collections
  of zero, one, or two operands use the evident zero-padded or pass-through
  representation. The eventual structure will recursively group larger
  collections in threes and apply `CarrySaveAdder` until at most two operands
  remain, but that grouping does not belong to the public semantic relation. A
  dedicated three-to-two tree description will probably be clearer than
  forcing this structure through the existing binary reduction tree.
  The experiment succeeded: a parent module consumes the tree's
  boundary preservation theorem directly, without learning the grouping or
  requiring a parallel deterministic contract. `UnsignedMultiply` is the
  first downstream test of that interface.
- `UnsignedMultiply` creates one ordinary partial-product row per multiplier
  bit, reduces the rows with `CarrySaveTree`, and combines the last two rows
  with the existing `Add`. With a result width equal to the sum of the operand
  widths, its public theorem gives exact natural-number multiplication.
- `ConditionalNegate` computes either a vector or its two's-complement negation
  using bitwise XOR with a broadcast control bit followed by `Add` with the
  control as carry-in. It should expose both bit-level and integer
  interpretation laws.
- `SignedMultiply` conditionally converts both inputs to unsigned magnitudes,
  applies `UnsignedMultiply`, and conditionally negates the full-width result
  according to the XOR of the operand signs. Its public theorem gives exact
  multiplication under two's-complement interpretation, including the
  most-negative input values.
- `VectorDelay` delays a vector by a statically known number of cycles using
  the existing generic `Register` hierarchy. Its contract relates output to
  the correspondingly earlier input without assuming initialized state before
  the delay has elapsed.
- `PipelinedSignedMultiply` supplies the multiplier interface required by the
  butterfly and proves that pipeline placement affects latency but not the
  product. A simple output delay may be useful first, but a useful high-speed
  structural multiplier will eventually need registers at selected
  carry-save-tree boundaries with all parallel paths kept aligned.

The implementation should reuse the existing `Mask`, `FullAdder`, `Add`,
`BitwiseXor`, `Constant`, `VectorLayout`, vector adapter, and generic `Register`
modules. Fixed shifts in partial products are layouts and do not require a
shift primitive.

The arithmetic support for this stack is not itself hardware. It includes a
two's-complement `BitVector.toInt`, sign and magnitude bounds, negation laws,
extension laws, multiplication bounds, and lemmas that turn modular equalities
into exact full-width multiplication results. These definitions should live in
the reusable Silean bit-vector foundation rather than under HTFFT.

The HTFFT-specific product truncation and binary-point adjustment must remain
outside the generic multiplier. They belong in the fixed-point layer that
selects the exact product slice used by the butterfly.

## Phase 2: fixed-point model and butterfly

Define a pure representation of the packed complex format and its exact
interpretation. The definitions must make explicit:

- real and imaginary component layout;
- component width and two's-complement range;
- binary-point position;
- the effect of increasing total complex width by two bits;
- multiplication result width;
- the selected truncation slice; and
- wrapping behavior wherever an operation is performed without extension.

Define a pure `fixedButterfly` that reproduces this behavior exactly. Then port
the pipelined butterfly into Silean and certify it against an exact cycle
contract. Pipeline settings should change latency but not the fixed-point
function computed for an aligned input triple.

Alongside exact certification, prove a local numerical lemma comparing the
decoded fixed-point butterfly with the ideal normalized butterfly. This first
lemma will test whether the proposed numerical representation and error style
are workable before they are propagated through a full FFT.

The butterfly is the first vertical milestone. It should emit compilable RTL
and be regression-tested against independently calculated examples.

## Phase 3: unrolled FFT

Port the recursive unrolled FFT construction into ordinary Lean definitions.
The likely form is a hierarchy containing two half-size transforms followed by
a layer of butterflies. Keep input bit reversal as a separately specified
permutation.

Prove in stages that:

1. the Silean hierarchy implements a pure recursive fixed-point transform;
2. bit reversal is the required permutation;
3. the corresponding exact-twiddle recursive transform computes the chosen DFT
   convention; and
4. quantized twiddles and arithmetic truncation introduce bounded error.

A concrete small transform, probably eight points, should be completed before
committing to the final generic proof interface. Generalization over an FFT
depth `k`, with size `2 ^ k`, is likely to be easier than using an arbitrary
size plus a power-of-two hypothesis.

## Phase 4: streaming stage

Port and certify one generic memory-backed FFT stage. Its public behavioral
contract should describe the logical data transformation and cycle schedule,
not merely repeat its internal counters and RAM contents.

The proof will need to account for:

- read and write indices;
- memory collision behavior;
- selection and swapping of memory data and new input data;
- twiddle selection;
- butterfly latency;
- reset or packet-boundary alignment; and
- output lane ordering.

The abstract contract state may differ substantially from the structural RAM
and counter state if that makes the invariant clearer.

## Phase 5: packet reordering and top level

Port the initial and final memory blocks with permutation-oriented packet
specifications. Compose them with the unrolled transform and remaining stages.

The initial top-level trace theorem should state, under a clearly documented
input protocol, that:

- each framed input packet contains exactly one `N`-sample vector;
- output framing identifies exactly one corresponding output packet;
- packets remain in order;
- the output packet equals the pure fixed-point FFT of the input packet; and
- the promised steady-state sample throughput is maintained.

Exact latency may be exposed as a parameter-dependent theorem, while the main
functional theorem should avoid unnecessary dependence on internal pipeline
placement.

## Phase 6: global accuracy theorem

Define a mathematical DFT with the same sign and indexing convention as the
hardware. The fixed-point representation grows at every butterfly while the
stored integer is not shifted, so the decoded output is expected to represent
a normalized transform. The exact scaling convention must be stated and proved
rather than inferred from tests.

The first global result should probably use a conservative pointwise maximum
error. Maintain explicit stage invariants for:

- maximum signal magnitude;
- accumulated arithmetic error;
- quantized-twiddle error;
- multiplication truncation error; and
- absence of unintended overflow or wraparound.

An RMS or sharper norm bound can follow once the conservative theorem is
complete. It may be useful to provide separate results relative to:

1. the mathematical values decoded from the actual input bits; and
2. pre-quantization mathematical inputs, adding an input-conversion term.

## Twiddle tables

Twiddle bit patterns are hardware data; their closeness to roots of unity is a
mathematical fact. Initially keep these concerns separate, for example with a
table and an associated accuracy certificate:

```lean
structure TwiddleTable where
  bits : Fin count -> ComplexBits width

structure TwiddleAccuracy (table : TwiddleTable ...) where
  error : forall index,
    norm (decode (table.bits index) - idealTwiddle index) <= delta
```

The precise definitions will depend on the available mathematical library and
how constants are generated. Possible approaches include Lean-generated
tables, checked rational interval certificates, or checked constants generated
by a small external tool. This choice is intentionally left open for now.

## Validation strategy

Proof is the primary objective, but generated-hardware regression remains
valuable. At useful milestones:

- build the Lean development without `sorry`, project axioms, or unsafe proof
  shortcuts;
- emit RTL and lower it through the supported toolchain;
- simulate against deterministic vectors and the existing `htfft` tests where
  their interface assumptions still match;
- inspect inferred multipliers and memories;
- compare latency, throughput, and resource use with the existing design; and
- add focused checks for theorem interfaces and recursive absence of
  blackboxes.

These tests validate tooling and synthesis expectations; they do not replace
the Silean structural certification.

## Near-term milestones

The tentative order is:

1. settle the exact fixed-point encoding and write executable examples;
2. add or select signed multiplication and pipeline-delay support;
3. implement and certify one butterfly;
4. prove a local butterfly error bound;
5. implement, certify, and emit a small unrolled FFT;
6. generalize the unrolled construction;
7. implement and certify one streaming stage;
8. implement the initial and final reordering memories;
9. compose and certify the complete streaming transform; and
10. prove and refine the global accuracy bound.

Milestones after the butterfly are deliberately subject to reordering.

## Open questions

The following should remain visible until experiments or proofs answer them:

- What exact parameter subset should the first complete transform support?
- Which arithmetic and memory operations belong in reusable Silean rather than
  in the client design?
- What primitive boundary gives good DSP and block-RAM inference?
- Should configurable pipeline placement be preserved initially or introduced
  after a single fixed pipeline is certified?
- What is the cleanest packet-level contract for a continuously streaming
  design without ready/valid signals?
- Which range invariant is sufficient to rule out unintended intermediate
  overflow?
- How should certified twiddle constants be produced?
- Should the mathematical accuracy development add a root Mathlib dependency
  or live in a small companion package?
- Which norm gives a useful first bound without making the initial proof
  disproportionately difficult?
- How much of the original parameter generator should become dependent Lean
  structure, and how much should remain explicit configuration data?

## Immediate next step

Inventory the current fixed-point behavior of the reference butterfly and the
relevant Silean arithmetic/emission facilities. From that, write the proposed
`ComplexBits`, signed decoding, fixed-point scaling, and exact `fixedButterfly`
definitions, together with small executable examples. Revisit this plan after
that experiment before fixing the wider hierarchy.
