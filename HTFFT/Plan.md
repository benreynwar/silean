# HTFFT port and verification plan

> **Status: provisional living document.**
>
> This records the current proof and implementation direction, not a frozen
> architecture. Update it when implementation experience changes a boundary or
> invalidates an assumption.

## Objective

Implement an FFT as a Silean client design, generate its RTL, and establish two
separate guarantees:

1. **Exact hardware refinement:** the Silean circuit implements a specified
   streaming fixed-point FFT, including arithmetic, ordering, state, framing,
   and latency.
2. **Numerical accuracy:** decoding that fixed-point result gives a value within
   a proved error bound of Mathlib's complex `ZMod.dft`.

The existing `htfft` VHDL and Python are design references, not specifications
that the new implementation must reproduce. We may deliberately correct or
improve their arithmetic and structure.

## Proof architecture

The intended theorem chain is:

```text
Silean streaming circuit
        |
        | exact structural, cycle, and trace refinement
        v
pure streaming fixed-point FFT
        |
        | exact packet/order correspondence
        v
pure fixed-point butterfly network
        |
        | decoding and numerical error bound
        v
exact complex butterfly network
        |
        | exact indexing and Cooley--Tukey theorems
        v
Mathlib ZMod.dft
```

Only the fixed-point-to-complex step is approximate. Hardware refinement and
all indexing, scheduling, and packet-ordering results should be exact.

Public specifications and contracts should use natural Lean mathematics.
Bit-level layouts, instance names, schedules, and proof bookkeeping belong in
structural or internal files unless they are genuinely part of the external
behavior.

## Initial scope

The first complete design should support:

- power-of-two radix-2 transforms;
- a power-of-two number of complex samples per cycle;
- packed signed fixed-point complex data;
- an unrolled FFT over the samples accepted together;
- memory-backed streaming stages for the remaining transform;
- explicit packet framing and a documented consecutive-input protocol;
- one-bit component-width growth at each butterfly layer; and
- synthesizable RTL with checked multiplier and memory inference.

Backpressure, arbitrary gaps, floating point, and configurable precision
trimming are outside the initial scope. Configurable internal pipeline
placement may be deferred until one fixed placement is certified.

## Settled decisions

These choices have been reviewed and should not be changed merely to simplify a
proof:

- Exact vectors use `Fin (2 ^ depth) → ℂ` and natural frequency ordering.
- Mathlib's unnormalized, negative-exponent `ZMod.dft` is the authoritative
  mathematical DFT. There is no project-local competing DFT definition.
- Recursive DIT splits input indices as `2*k` and `2*k+1`. A butterfly writes
  its sum at `k` and difference at `k + 2^depth`; no final permutation is
  required for the recursive transform.
- Fixed-point formats carry component width and fractional-bit count
  independently. Growing the width does not implicitly move the binary point.
  With the current policy, decoded butterfly layers therefore represent the
  **unnormalized** transform unless an explicit rescaling operation is added.
- Pure fixed-point values are scaled `Int`s. Representability and absence of
  overflow are propositions rather than being hidden in the value type.
- Complex multiplication combines each real or imaginary numerator at full
  integer precision and rounds once. The initial rounding policy is nearest
  with ties to even.
- Wrapping is explicit. Useful accuracy theorems will assume and prove suitable
  no-overflow conditions rather than treating modular wrap as a small error.

## Current state

### Pure fixed-point arithmetic

Completed files are:

- `HTFFT/Complex.lean`: a small generic complex-number vocabulary;
- `HTFFT/FixedPoint.lean`: formats, exact rational decoding, quantization,
  rounding, rescaling, representability, and explicit wrapping; and
- `HTFFT/FixedPoint/Correctness.lean`: exact and bounded decoding laws for
  rescaling, quantization, arithmetic, and non-wrapping values; and
- `HTFFT/Butterfly.lean`: exact and fixed-point butterflies, a concrete
  no-overflow predicate, and the shape of a local error statement; and
- `HTFFT/Fixed/ButterflyCorrectness.lean`: the local no-overflow and numerical
  error theorems for the fixed-point butterfly.

Focused tests cover signed wrapping, binary-point preservation, negative and
ties-to-even rounding, grid-aligned exact cases, and fused complex-product
rounding.

### Exact recursive FFT and DFT theorem

Completed files are:

- `HTFFT/Exact/Indexing.lean`: power-of-two vectors, even/odd splitting,
  concatenation of equal halves, and fixed-width bit reversal; and
- `HTFFT/Exact/Radix2.lean`: the canonical `Fin`/`ZMod` index equivalence,
  exact negative-exponent twiddles, recursive DIT FFT, public half-evaluation
  laws, and the pointwise correctness proposition; and
- `HTFFT/Exact/DFT.lean`: Fourier-coefficient identities, the even/odd
  Cooley--Tukey equations for both output halves, and the inductive proof that
  the recursive transform equals `ZMod.dft` pointwise.

Indexing checks cover depths zero through three. Exact checks include the
length-one identity, the length-two sum/difference transform, and known impulse
transforms at sizes two, four, and eight. Mathlib is pinned to `v4.32.1`,
matching the project's Lean `4.32.1` toolchain.

### Exact hardware-shaped layered network

The exact layered-network foundation is complete. `HTFFT/Exact/Layered.lean`
reuses the existing exact vector, bit reversal, and twiddle definitions. A
`LayerPosition` exposes each stage as a contiguous group, a sum/difference
branch, and an offset shared by one butterfly pair. Stage `s` pairs positions
`2^s` apart, uses the length-`2^(s+1)` twiddle selected by the shared offset,
and writes the sum before the difference.

`layeredFFT` first bit-reverses the input and then folds stages in ascending
order, from adjacent pairs through the full-vector layer. Its result is
declared in natural-frequency order and has no final permutation. The
explicit stage list and its append law allow the same pure network to be split
later into combinational and memory-backed portions without putting timing or
storage into this specification. `LayerBoundary`, `layeredPrefix`, and
`layeredFFT_split` give that split a typed public interface at every boundary
from zero through the complete transform.

`HTFFT/Exact/LayeredCorrectness.lean` proves the semantic prefix invariant:
every nonfinal prefix at successor depth is two independent lower-depth
prefixes over the even and odd inputs. The final layer uses exactly the
recursive combine indexing and twiddles. Induction therefore proves
`layeredFFT_eq_radix2`, and `layeredFFT_agreesWithDFT` connects the result to
Mathlib's unnormalized negative-exponent `ZMod.dft` in natural frequency order.

Executable checks enumerate every layer position through depth three. Exact
checks cover the depth-zero identity, the complete depth-one butterfly,
offset-zero butterfly arithmetic at depths two and three, the DC output of the
complete four- and eight-point layer chains, every split boundary of a
three-stage network, and exact impulse transforms through depth three.

The combined `lake build Silean SileanTests HTFFT HTFFTTests` gate passes
3,876 jobs as of 2026-09-21.

### Pure fixed-point layered network

The public network and its numerical proof are complete.
`HTFFT/Fixed/Layered.lean` defines a `Config` assigning a data format to every
layer boundary, so stage `s` consumes boundary `s` and produces boundary `s+1`
by construction. Product and twiddle formats and rounding modes remain
stage-dependent.

`TwiddleTable` contains only stored integer values. The separate
`TwiddleAccuracy` proposition records representability and a uniform error for
each stage against the exact root of unity. The pure fixed-point layer reuses
the exact network's group/branch/offset indexing, bit reversal, and ascending
stage list. Prefix, suffix, split, and complete-network operations therefore
have the same shape as the exact layered model, without clocks or storage.

The uniform bounds are represented by `Bounds`, with scalar Euclidean complex
`magnitude` (`M_s`) and `error` (`E_s`) fields. `advanceBounds` uses

```text
M_(s+1) = 2 M_s
E_(s+1) = (2 + delta_s) E_s
            + M_s delta_s
            + R_s
```

where `delta_s` is the stored-twiddle error and `R_s` is the local fixed-point
rounding allowance, all measured in ordinary complex magnitude. Exact FFT
twiddles have norm one, so multiplication by them does not amplify error.
`HTFFT/Fixed/Error.lean` proves the supporting generic norm laws and converts
the componentwise fixed-point and rectangular-enclosure facts to Euclidean
bounds with the exact factor `sqrt 2`. `HTFFT/Fixed/LayeredCorrectness.lean`
lifts the local
butterfly theorem through every prefix and proves complete-network bounds
against both the exact layered FFT and Mathlib's DFT. Its corollaries cover
decoded input bits (initial error zero), an arbitrary pre-quantization error,
and inputs produced by the fixed-point quantizer (`sqrt 2` times one component
LSB). The same
induction proves that every result is representable under the explicit
no-overflow hypothesis.

The magnitude recurrence has the proved closed form `M_s = 2^s M_0`. With
exact twiddles and a constant local allowance `R`, the error recurrence has
the proved closed form

```text
E_s = 2^s E_0 + (2^s - 1) R.
```

Thus its baseline growth is linear in transform size `N = 2^s`, rather than
the previous componentwise proof's `3^s = N^(log_2 3)`. Nonzero twiddle errors
remain explicit in the recurrence rather than changing this hidden norm
constant.

The current `R_s` deliberately charges the generic worst-case rounding
allowance at every stage. A later refinement may certify smaller stage-specific
bounds—including zero arithmetic error for stages whose exact `1` and `-i`
twiddles only discard zero bits, and a half-LSB bound for nearest rounding—but
this is not required for the first end-to-end accuracy theorem.

The formats already permit stage-dependent fractional-bit counts. A later
width/accuracy trade-off should use this recurrence to decide where low bits
may be discarded: a rounding error introduced at boundary `s` must be charged
for its amplification through the remaining layers. This supports fixed-width
schedules such as trading one fractional bit for one integer-growth bit, but
the schedule should be selected from an explicit final error budget rather
than from the old loose componentwise bound.

### Concrete eight-point numerical theorem

The first pure end-to-end numerical instance is complete. The reusable range
layer is split by responsibility:

- `HTFFT/FixedPoint/Range.lean` converts symmetric raw component bounds into
  representability and supplies conservative rounded-division bounds;
- `HTFFT/Fixed/ButterflyRange.lean` proves that one initial-policy butterfly
  maps a raw component bound `B` to `3*B+1` while discharging every internal
  no-wrap boundary; and
- `HTFFT/Fixed/LayeredRange.lean` composes that result across arbitrary layer
  prefixes and derives the network's trace-shaped `NoOverflow` proposition
  from a uniform input bound and static format capacities.

`HTFFT/Fixed/Twiddle8Accuracy.lean` instantiates those generic results for the
certified table. Its public decoded-input assumption is the natural statement
`MagnitudeBound 1 (decodeVector config 0 input)`, not an internal overflow
trace. The Q4.8 input has raw component bound `256`; conservative prefix bounds
are `256`, `769`, `2308`, and `6925`, all supported by the one-bit-per-stage
growth policy. The generated Q2.8 twiddles have raw component magnitude at
most `256`.

For decoded inputs with Euclidean magnitude at most one, the theorem compares
the Q7.8 output pointwise with Mathlib's unnormalized `ZMod.dft` in
natural-frequency order and proves the Euclidean error bound

```text
25 * sqrt 2 / 256 + 9 / 32768 ≈ 0.138381.
```

For intended rational inputs of Euclidean magnitude at most one, a second
theorem includes the conservative `sqrt 2 / 256` input quantization error. It
proves

```text
33 * sqrt 2 / 256 + 13 / 32768 ≈ 0.182698.
```

The certified Euclidean twiddle errors are `0`, `0`, and `sqrt 2 / 256`.
The encoded-input corollary separately uses the componentwise quantizer fact
to retain raw bound `257` for range certification. Sharpening exact early-stage
arithmetic remains deferred rather than being mixed into this generic
improvement.

### Reusable signed precision reduction

The first hardware arithmetic needed by the packed butterfly is complete.
`Silean/Modules/SignedRoundShift` specifies an ordinary signed-integer
operation: divide by a static power of two, round to nearest with ties to even,
and encode at the retained width. The public contract is deliberately not
about fixed-point formats. Its structural implementation uses fixed wiring for
the retained, guard, sticky, and quotient-parity bits, followed by a certified
incrementer and mux. The proof covers negative inputs, zero retained or
discarded widths, and output wrapping.

`HTFFT/Silean/SignedRoundShift.lean` is the separate client bridge showing that
this integer operation agrees with the pure fixed-point `roundRatio` and
`encodeSigned` vocabulary. The module has only a structural implementation;
no duplicate authored construction was introduced. Focused contract,
hierarchy, and FIRRTL checks pass, as does the complete `SileanTests` target.

The reusable addition hierarchy is also ready for the packed butterfly.
Equal-width carry-aware building blocks are explicitly named `AddWithCarry`
and `AddSubWithCarry`. General structural `Add`, `Sub`, and runtime-selectable
`AddSub` modules accept independent operand widths, per-operand static
signedness, and extended or truncating output. Their natural contracts use
ordinary integer arithmetic followed by one explicit fixed-width encoding;
the structural proofs connect sign/zero extension and the carry-aware children
to those contracts. Circuit arithmetic notation now places these real modules
instead of expanding an inline recipe.

### Project-specific pipelined complex multiplication

The first HTFFT-specific structural arithmetic block is complete under
`HTFFT/Silean/PipelinedSignedComplexMultiply/`. It deliberately does not live
in `Silean/Modules`: the choice of four scalar products, fused real and
imaginary numerators, one nearest-even reduction per completed component, and
their common latency is part of the HTFFT arithmetic architecture rather than
a general framework primitive.

Its public trace contract interprets four component ports as signed integers,
computes

```text
aReal * bReal - aImag * bImag
aReal * bImag + aImag * bReal
```

at full precision, rounds each completed numerator exactly once, and relates
every available output to the input at the selected static latency. The
structure uses four equal-latency `PipelinedSignedMultiply` children, an
extended signed `Sub` and `Add`, two wire-only width normalizations, and two
`SignedRoundShift` children. Its width API is total for all natural parameters:
the numerator has one bit beyond the scalar-product width, retained width uses
saturating Nat subtraction, and an excessive discard request therefore yields
a zero-width result rather than an extra high-bit truncation policy.

The certification proof uses only the public structural and execution
interfaces of those children. It extracts the four multiplier traces together
from each parent execution so product alignment is preserved, then proves the
natural delayed contract. The separate
`HTFFT/Silean/PipelinedSignedComplexMultiply.lean` bridge shows that decoded
contract results equal `Butterfly.Fixed.multiplyRounded` when fractional-bit
positions match the selected discard and the unwrapped components fit the
hardware result width. Focused checks cover zero and positive latency,
asymmetric and zero widths, excessive discard, positive and negative ties,
placement, hierarchy closure, FIRRTL shape, and the fixed-point bridge.

### Project-specific pipelined fixed-point butterfly

The complete packed butterfly is implemented under
`HTFFT/Silean/PipelinedFixedButterfly/`. Its public contract is the natural
pure `Butterfly.Fixed.butterfly` calculation over decoded packed inputs, with
the upper and lower complex results encoded at the output boundary. The
contract contains no child wires or register state.

The width policy is now explicit. A `w`-bit data component and its twiddle are
multiplied with fused full-precision numerators, rounded once back to the data
binary point, and narrowed or wrapped at the `w`-bit product boundary. The
final signed Add/Sub extends to `w+1` bits. The fractional-bit count is
unchanged and there is no post-addition low-bit trimming. A static carrier
condition states when the generic complex-multiplier output contains the whole
selected product boundary.

The structural pipeline has synchronized optional input registers, the nested
complex-multiplier latency and optional pre-rounding register, an optional
completed-product register, exact delay of the `a` path, and synchronized
optional output registers. Structural certification and the all-time trace
theorem use only public child interfaces. The unconditional decoded theorem
equals the wrapped pure butterfly; a second theorem removes the wraps under
the pure model's `NoOverflow` hypothesis. Focused checks cover all sixteen
optional-stage combinations, arithmetic and ties, an actual fully pipelined
execution, zero-width closure, placement, hierarchy, and FIRRTL shape.

## Remaining work

### 1. Define and bound the pure fixed-point network

1. [x] Instantiate the same topology with the fixed-point butterfly and stored
   twiddle values.
2. [x] Define the decoding relation from each fixed format to complex values.
3. [x] Prove a local butterfly bound accounting for:
   - existing error in both inputs;
   - twiddle quantization error;
   - multiplication and addition rounding; and
   - the no-overflow hypotheses needed to exclude wraparound.
4. [x] Track both a magnitude bound and an error bound through every layer. The
   magnitude invariant is required because twiddle error is multiplied by the
   data magnitude.
5. [x] Compose the layer bounds into a pointwise bound for the complete fixed-point
   network.

Error and mathematical magnitude propagation now use ordinary complex
magnitude. Componentwise bounds remain only at fixed-width representability
and rectangular certificate boundaries.

Provide two numerical statements where useful:

- error relative to the exact values decoded from the actual input bits; and
- error relative to pre-quantization inputs, with input quantization added as a
  separate term.

### 2. Certify twiddle tables

The first generation and certification path is complete.
`HTFFT/Fixed/TwiddleTable.lean` keeps three roles separate:

- `RationalTwiddleTable` is executable rational approximation data;
- `quantizeTwiddleTable` generates stored integers from explicit per-stage
  formats and rounding modes; and
- `TwiddleEnclosure` is a kernel-checked componentwise interval certificate
  against the existing exact roots of unity.

`twiddleAccuracy_of_enclosure` composes an enclosure, fixed-point quantization,
and a representability proof into the `TwiddleAccuracy` interface used by the
network theorem. Approximation data may therefore be produced inside Lean or
externally, but it is trusted only after Lean checks the enclosure.

`HTFFT/Fixed/Twiddle8.lean` provides the first concrete instance. It generates
the complete Q2.8 table for an eight-point FFT. Mathlib's exact trigonometric
identities reduce the nontrivial roots to `sqrt 2 / 2`; rational square bounds
certify `181 / 256 ≤ sqrt 2 / 2 ≤ 182 / 256`. Every generated entry is
representable, every rational center is encoded exactly, and the resulting
per-stage enclosure radii are `0`, `0`, and `1 / 256`. Their certified
Euclidean `TwiddleAccuracy` errors are `0`, `0`, and `sqrt 2 / 256`.

### 3. Implement and certify the Silean butterfly and unrolled FFT

1. [x] Implement and certify the fused pipelined signed complex multiplier,
   including its fixed-point semantic bridge.
2. [x] Implement the remainder of the packed fixed-point butterfly using reusable
   Silean arithmetic and the certified multiplier.
3. [x] Prove exact correspondence with the pure fixed-point butterfly, including
   every slice, extension, rounding, and pipeline delay.
4. Build the unrolled FFT from certified butterflies, reindexing, constants,
   and registers.
5. Prove exact correspondence with the pure fixed-point network.
6. Emit and inspect a small transform before generalizing parameters.

Pipeline placement affects latency and timing structure, not the mathematical
result. Optimize it behind the public multiplication theorem when synthesis
results justify doing so.

### 4. Implement and certify streaming stages

Give each memory-backed stage a natural data-transformation and cycle-schedule
contract. Its invariant must cover:

- read and write indices;
- memory collision semantics;
- selection between stored and newly arriving data;
- twiddle selection;
- butterfly and memory latency;
- reset or packet-boundary alignment; and
- lane and sample ordering.

Choose the memory primitive boundary based on both proof quality and generated
RAM inference. The abstract contract state need not mirror structural RAMs and
counters.

### 5. Compose packet reordering and the top level

Specify initial and final reorderers as packet permutations, then prove that:

- each accepted frame denotes one complete input vector;
- output framing identifies one corresponding output vector;
- packets remain in order;
- the output packet equals the pure fixed-point FFT result; and
- the promised steady-state throughput and stated latency hold.

The first protocol may require consecutive packet samples and may omit
ready/valid backpressure, but those environmental assumptions must be explicit.

### 6. State the final accuracy theorem

Compose the exact hardware theorem, packet correspondence, fixed-point error
bound, exact-network equivalence, and recursive DFT theorem. The result should
have the schematic form:

```text
valid input protocol
∧ representable inputs
∧ certified twiddles
∧ proved no-overflow bounds
→ norm (decode (hardwareOutput packet) - ZMod.dft input) ≤ globalErrorBound
```

The theorem must state the precise input interpretation, output scaling,
ordering, latency, and norm. With the currently selected constant fractional
bit count, the target is the unnormalized DFT.

## Milestones

- [x] Pure fixed-point representation and butterfly specification.
- [x] Exact indexing, twiddle, and recursive radix-2 interfaces.
- [x] One-step Cooley--Tukey theorem and recursive equality with `ZMod.dft`.
- [x] Exact bit-reversed iterative-network interface and depth-zero-through-three checks.
- [x] Prefix/suffix decomposition and equality of the layered network with the recursive FFT and DFT.
- [x] Local and network-wide fixed-point magnitude/error bounds.
- [x] Certified twiddle-table generator and concrete eight-point Q2.8 table.
- [x] Concrete eight-point no-overflow derivation and pointwise numerical
  bounds against Mathlib's DFT, for both decoded and pre-quantization inputs.
- [x] Certified Silean butterfly.
- [ ] Certified and emitted small unrolled FFT, then generalized construction.
- [ ] Certified streaming stage and memory primitive.
- [ ] Packet reorderers and composed streaming FFT.
- [ ] Final end-to-end accuracy theorem.
- [ ] Repository-wide proof-trust audit: review and replace production uses of
  `native_decide` and check for other unsafe or non-kernel-checked proof
  shortcuts. Existing occurrences are concentrated in `PicoRV/` and
  `SailBridge/`; uses confined to tests and executable examples are acceptable.

## Validation policy

At each relevant milestone:

- build without `sorry`, project axioms, or unsafe proof shortcuts;
- do not introduce `native_decide` into production proofs;
- add focused executable and theorem-interface regressions;
- verify the reusable `Silean` and `SileanTests` targets remain green;
- close and inspect the generated module hierarchy;
- emit and lower RTL;
- simulate deterministic vectors;
- inspect multiplier and RAM inference; and
- compare latency, throughput, and resource use with the reference design where
  the comparison remains meaningful.

Simulation and comparison are supporting evidence, not substitutes for
structural certification.

## Open decisions

- What transform sizes and samples-per-cycle configurations define the first
  complete supported subset?
- What internal multiplier pipeline placement gives acceptable timing?
- What memory primitive and collision semantics give both a clean proof and
  reliable block-RAM inference?
- What packet contract best describes continuous operation without
  ready/valid signals?
- When should the checked rational-enclosure input be automated by an external
  certificate generator for larger tables?
- Which stage-dependent fractional-bit schedule gives the best width/accuracy
  trade-off for the first hardware configuration?
- Which configuration data should become dependent Lean structure, and which
  should remain explicit parameters?

## Immediate next step

Define the first small unrolled Silean FFT from the certified butterfly,
bit-reversal wiring, certified twiddle constants, and explicit inter-stage
register placement. Keep stage-dependent fractional-bit scheduling as an
explicit reviewed configuration decision rather than silently trimming low
bits inside the butterfly.
