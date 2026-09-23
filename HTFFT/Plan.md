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
- Conditional top-level and stage-chain bodies and proofs, including the
  zero-rolled-stage case.
- Generic pure scheduling semantics and correctness for one rolled
  `FFTStage`.

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

The conditional top-level proof already establishes that the four functional
children plus the separate marker delay implement the pure fixed-point FFT,
assuming their public contracts. The conditional `FFTStageChain` proof applies
the rolled suffix from one `FFTStage` contract per layer. Neither proof inspects
child state or implementation details.

## Current focus: concrete `FFTStage`

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

The remaining work for the concrete stage is:

1. Define its permanent structural child hierarchy from explicit shift
   registers, phase control, muxes, the certified twiddle ROM, and a parallel
   bank of certified butterflies.
2. State the exact structural latency from `pairDelay`, butterfly latency, and
   any deliberately selected alignment registers.
3. Prove that concrete execution exposes the pure bank signals, using only the
   public contracts of the children.
4. Apply the completed scheduling theorem to discharge the public framed
   `FFTStage` contract.
5. Add focused generic checks plus at least one closed configuration with
   hierarchy inspection, FIRRTL emission, and deterministic simulation.

Do not change the natural stage contract to fit the structure. If refinement
is awkward, first check whether the structural or trace framework is missing a
reusable composition theorem.

## Work after the concrete stage

### 1. Implement and certify the packet reorderers

Implement `InitialReorder` and `FinalReorder` with explicit shift-register
storage against their existing framed packet-permutation contracts. Their
proofs must expose only cycle/lane-to-logical-index correspondence, latency,
and marker behavior—not internal storage state.

### 2. Close the hierarchy

Replace the unresolved stage, initial-reorder, and final-reorder children with
their verified Silean designs. Reuse the existing top-level and stage-chain
bodies and discharge their explicit child-contract hypotheses. Then:

- close and inspect the complete `ModuleStructure` hierarchy;
- emit and lower RTL;
- simulate deterministic complete frames; and
- confirm latency, throughput, arithmetic widths, shift-register structure,
  and multiplier lowering.

### 3. Prove the final accuracy theorem

Compose:

- exact concrete-hardware refinement;
- top-level frame and ordering correspondence;
- fixed-point network correctness and no-overflow proof;
- the global fixed-point error bound; and
- equality of the exact layered FFT with Mathlib's DFT.

The final theorem should have the shape

```text
valid input protocol
∧ representable inputs
∧ certified twiddles
∧ proved no-overflow conditions
→ norm (decode (hardware output) - ZMod.dft input) ≤ global error bound.
```

It must state the input interpretation, natural output ordering, latency,
unnormalized scaling, and norm explicitly.

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
- [ ] Certified concrete shift-register `FFTStage`.
- [ ] Certified initial and final packet reorderers.
- [ ] Closed composed streaming FFT hierarchy and RTL regression.
- [ ] Final end-to-end hardware-to-DFT accuracy theorem.
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

Implement the structural child hierarchy of the generic `FFTStage` and prove
its execution refines the completed pure commutator-bank schedule. Keep the
existing natural stage contract and conditional `FFTStageChain` proof
unchanged.
