# HTFFT port and verification roadmap

> **Status: provisional living document.**
>
> This records the current proof and implementation direction, not a frozen
> architecture. Update it when implementation experience changes a boundary or
> invalidates an assumption.

## Objective

Implement a power-of-two radix-2 FFT as a Silean client design, generate its
RTL, and establish two separate guarantees:

1. **Exact hardware refinement:** the Silean circuit implements a specified
   streaming fixed-point FFT, including arithmetic, ordering, framing, and
   latency.
2. **Numerical accuracy:** decoding that fixed-point result is within a proved
   error bound of Mathlib's complex `ZMod.dft`.

The existing `htfft` VHDL and Python are design references, not specifications.
The Lean/Silean design may correct or improve them.

## Proof architecture

```text
Silean streaming circuit
        |
        | exact structural, cycle, and trace refinement
        v
pure streaming fixed-point FFT
        |
        | exact frame-layout and ordering correspondence
        v
pure fixed-point butterfly network
        |
        | decoding and numerical error bound
        v
exact complex butterfly network
        |
        | exact Cooley--Tukey and indexing theorems
        v
Mathlib ZMod.dft
```

Only the fixed-point-to-complex step is approximate. Hardware refinement,
scheduling, framing, indexing, and ordering results are exact.

Public contracts should use natural Lean mathematics. Bit layouts, instance
names, schedules, and proof bookkeeping belong in structural or internal files
unless they are part of externally observable behavior.

## Supported subset and deferred features

The first complete design supports:

- power-of-two radix-2 transforms;
- a power-of-two number of packed complex samples per cycle;
- signed fixed-point components;
- an unrolled prefix over samples accepted together;
- shift-register-based rolled stages for the remaining layers;
- consecutive cycles within a frame, with explicit frame markers; and
- one high-bit of component-width growth per butterfly layer, with a fixed
  binary-point position.

The following are deferred:

- ready/valid backpressure and gaps within a frame;
- RAM-backed delay storage or RAM inference;
- floating point;
- low-bit trimming or stage-dependent rescaling;
- timing-driven pipeline optimization beyond a first certified placement; and
- external-module substitution.

## Settled design decisions

- Exact vectors use `Fin (2 ^ depth) → ℂ` in natural frequency order.
- Mathlib's unnormalized negative-exponent `ZMod.dft` is authoritative; there
  is no project-local competing DFT definition.
- The exact recursive DIT transform splits even and odd inputs, writes sums in
  the lower output half and differences in the upper half, and needs no final
  permutation.
- The hardware-shaped layered network bit-reverses once before ascending
  butterfly stages and finishes in natural frequency order.
- Fixed-point values are scaled `Int`s. Width and fractional-bit count are
  independent. Representability and absence of overflow are explicit
  propositions.
- A concrete streaming `FFT.Configuration` owns its rational twiddle
  approximations and per-stage quantization policy, and derives its stored
  `twiddleTable` from them. Lower pure fixed-point, unrolled-network, and
  individual-stage models remain parameterized by arbitrary tables so they
  stay reusable and easy to reason about.
- The current format policy keeps fractional bits fixed and grows the high side
  by one bit per butterfly layer. The transform is unnormalized.
- Complex multiplication forms each real or imaginary numerator at full
  precision and rounds once, initially using nearest with ties to even.
- Wrapping is explicit. Accuracy theorems assume and prove the no-overflow
  conditions required to exclude it.
- Rolled-stage delay storage is built from explicit shift registers.
- Structural modules are sufficient unless an authored construction has a
  clear human-facing benefit.
- Unresolved children in a `ModuleBody` do not receive invented execution
  semantics. Conditional parent proofs use synchronized body traces, wiring,
  and explicit child-contract hypotheses. The body is reused when concrete
  children replace the unresolved declarations.

## Verified foundation

The following layers are complete and reusable:

- Exact recursive FFT, exact hardware-shaped layered FFT, and pointwise
  equality with Mathlib's `ZMod.dft`.
- Pure fixed-point butterfly and layered network, explicit no-overflow
  conditions, and network-wide magnitude and Euclidean error propagation.
- Kernel-checked twiddle-table generation and certification, including a
  concrete eight-point Q2.8 instance with no-overflow and numerical bounds.
- Reusable structural signed add, subtract, add/subtract, multiplication,
  shift registers, ROM, and nearest-even signed precision reduction.
- Certified pipelined signed complex multiplication and packed fixed-point
  butterfly.
- Generic certified unrolled FFT layers and network, including the fixed-point
  and DFT bridges.
- Reusable fixed-latency and framed-latency trace composition.
- Implementation-independent `ModuleBody` traces, wiring semantics, and the
  bridge from concrete composite execution.
- Natural top-level FFT, packet-reorderer, `FFTStageChain`, and individual
  `FFTStage` contracts.
- Conditional top-level body and proof, including the zero-rolled-stage case.
- Concrete certified `FFTStageChain`, composed from one certified concrete
  `FFTStage` per rolled layer.
- Generic pure scheduling semantics and correctness for one rolled
  `FFTStage`.
- Concrete certified `InitialReorder`, built from pipelined barrel shifters
  and read-old register banks and proved against its natural framed global
  bit-reversal contract.
- Concrete certified `FinalReorder`, built from two read-old register banks,
  half-vector routing, collision bypass, and marker alignment. Its public
  theorem proves the natural final-layout permutation for valid frames,
  including continuously adjacent frames.
- Closed concrete top-level `FFT` hierarchy. Its public execution theorem
  composes the certified reorderers, unrolled prefix, marker delay, and rolled
  stage chain into the existing natural framed fixed-point FFT contract.
- End-to-end concrete-execution accuracy theorem. For every valid marked
  frame, it states the exact output latency and natural ordering and bounds
  each decoded hardware result against Mathlib's unnormalized `ZMod.dft` by
  the explicit global fixed-point error recurrence. Its coefficient premise
  certifies the table generated by the same concrete configuration used to
  construct the hierarchy; the public concrete APIs no longer accept a
  second, potentially inconsistent table argument.

The fixed-point network tracks magnitude `M_s` and error `E_s` in ordinary
complex norm. For twiddle error `delta_s` and local arithmetic allowance
`R_s`, one layer satisfies

```text
M_(s+1) = 2 M_s
E_(s+1) = (2 + delta_s) E_s + M_s delta_s + R_s.
```

With exact twiddles and constant `R`, this specializes to
`E_s = 2^s E_0 + (2^s - 1) R`. This is the baseline bound for the first closed
hardware configuration. Sharper stage-specific rounding bounds and precision
trimming remain later refinements.

## Streaming architecture and protocol

The top-level data path is:

```text
InitialReorder
    -> UnrolledFFTNetwork at laneDepth
    -> FFTStageChain
    -> FinalReorder
```

`InitialReorder` performs the global input bit reversal. The unrolled network
therefore consumes already-reordered values directly. `FFTStageChain` applies
the remaining rolled butterfly layers. `FinalReorder` converts the last
streamed layout to natural frequency order.

The unrolled network carries data only. A separate `OptionalShiftRegister` of
the same latency carries its frame marker. This keeps the already-certified
unrolled data contract unchanged.

`i_first` marks the first cycle of a candidate input frame, and `o_first` marks
the corresponding first output cycle. A contract obligation exists only when
the remaining cycles of that input frame contain no second `i_first`. An early
new marker invalidates the interrupted frame; it may independently begin a new
valid frame. There is no reset requirement at this boundary, and outputs before
a valid frame's guaranteed output window are unspecified.

The top-level hierarchy is now fully concrete. Its execution theorem obtains
the public contracts of the four functional children and the separate marker
delay, then applies the existing conditional composition proof to establish
the pure fixed-point FFT contract. `FFTStageChain` similarly obtains one
public `FFTStage` contract per rolled layer. Neither proof inspects child state
or implementation details.

## Completed milestone: concrete `FFTStage`

The pure scheduling model and proof are complete in:

- `HTFFT/Silean/FFTStage/Internal/FFTStageSchedule.lean`; and
- `HTFFT/Silean/FFTStage/Internal/FFTStageScheduleCorrectness.lean`.

For arbitrary valid geometry, arbitrary initial phase, and arbitrary delay-line
contents, an input frame beginning with `i_first`:

- rephases input routing on the marked cycle;
- becomes independent of the prior delay contents after `pairDelay` cycles;
- produces the exact butterfly operand pair at every lane and output cycle;
- delays the frame marker to the correct output window;
- associates every pair with the correct output position and twiddle address;
  and
- evaluates to `encodeOutputFrame (resultValue ...)` over the complete frame.

The input routing phase and output-period phase are deliberately separate. The
input phase rephases immediately on `i_first`; the marker delayed by
`pairDelay` starts the output phase. A following input frame can therefore
start while the preceding frame's tail is emerging without changing the
preceding frame's twiddle selection.

For `D = pairDelay`, each commutator lane uses two `D`-cycle delay paths:

```text
input phase   delay-1 input   delay-2 input   butterfly operands
first half    current A       current B       delay-2 out, delay-1 out
second half   current B       delay-2 out     delay-1 out, current A
```

The concrete stage now has:

- a permanent structural hierarchy built from the input splitter, shared phase
  control, explicit per-lane shift registers, certified twiddle ROMs and
  butterflies, output combiner, and marker alignment register;
- exact latency `pairDelay + butterfly latency`;
- a state-hidden refinement from every concrete execution to the pure
  commutator-bank schedule, including arbitrary state accumulated before a
  valid frame; and
- a public theorem that every concrete execution satisfies the unchanged
  natural framed `FFTStage` contract.

Focused interface checks are present. Closed hierarchy inspection, RTL
emission, and deterministic simulation remain part of the later composed RTL
regression rather than this proof milestone.

Do not change the natural stage contract to fit the structure. If refinement
is awkward, first check whether the structural or trace framework is missing a
reusable composition theorem.

## End-to-end theorem

The proved public theorem has the shape

```text
valid input protocol
∧ fixed-width input interpreted within the stated initial error
∧ certified twiddles
∧ proved no-overflow conditions
→ norm (decode (hardware output) - ZMod.dft input) ≤ global error bound.
```

It states the input interpretation, natural output ordering, exact latency,
unnormalized scaling, pointwise complex norm, and propagated bound explicitly.

## Remaining work

### 1. Validate the closed hierarchy

Choose the first closed numerical and pipeline configuration, then:

- inspect the complete `ModuleStructure` hierarchy;
- emit and lower RTL;
- simulate deterministic complete frames; and
- confirm latency, throughput, arithmetic widths, shift-register structure,
  and multiplier lowering.

## Milestones

- [x] Exact radix-2 FFT and equality with Mathlib's DFT.
- [x] Hardware-shaped layered exact FFT and prefix/suffix decomposition.
- [x] Pure fixed-point network and global numerical bounds.
- [x] Certified twiddle generation and concrete eight-point theorem.
- [x] Certified Silean arithmetic, complex multiply, and butterfly.
- [x] Generic certified unrolled FFT.
- [x] Streaming layouts and natural framed contracts.
- [x] Conditional top-level FFT and `FFTStageChain` hierarchy proofs.
- [x] Generic pure rolled-stage scheduling and full-frame correctness.
- [x] Certified concrete shift-register `FFTStage`.
- [x] Concrete certified generic `FFTStageChain`.
- [x] Certified initial packet reorderer.
- [x] Certified final packet reorderer.
- [x] Closed and certified composed streaming FFT hierarchy.
- [x] Configuration-owned concrete twiddle generation throughout the closed
  hierarchy, while retaining arbitrary-table lower-level models.
- [ ] Complete-hierarchy RTL emission and deterministic regression.
- [x] Final end-to-end hardware-to-DFT accuracy theorem.
- [ ] Repository-wide proof-trust audit. Production proofs must not use
  `native_decide`, `sorry`, project axioms, or unsafe proof shortcuts; tests and
  executable examples may use appropriate evaluation mechanisms.

## Validation policy

At each relevant milestone:

- build the affected library and test aggregates;
- keep production proofs kernel-checkable and free of placeholders;
- add focused theorem-interface and executable regressions;
- prove structures from public child interfaces;
- inspect closed module hierarchies;
- emit and lower RTL;
- simulate deterministic vectors; and
- compare latency, throughput, and resource structure with the reference
  design where that comparison remains meaningful.

Simulation and comparison are supporting evidence, not substitutes for
structural certification.

## Open decisions

- Which transform size and samples-per-cycle configuration should be the first
  complete closed RTL target?
- Which fixed butterfly pipeline placement should that target use?
- What explicit minimum spacing between valid frames should the first top-level
  protocol guarantee?
- Which stage-dependent fractional-bit schedule, if any, should follow the
  initial constant-fractional-bit implementation?

## Immediate next step

Select a modest complete FFT configuration and inspect its emitted hierarchy,
then emit and lower RTL and run deterministic complete-frame regressions.
