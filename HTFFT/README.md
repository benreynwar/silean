# HTFFT

HTFFT is the main client design used to develop and test Silean. It is a
Lean/Silean implementation of the fixed-point streaming FFT in
[benreynwar/htfft](https://github.com/benreynwar/htfft). The VHDL and Python
implementation is a design reference, not the specification: the authoritative
behavior is stated in Lean.

The current design implements a power-of-two radix-2 FFT with a power-of-two
number of packed complex samples per cycle. Components are signed fixed-point
integers. The binary-point position remains fixed, and the component width
grows by one high bit at each butterfly layer.

## Proof boundary

The main proof is deliberately layered:

```text
concrete Silean streaming circuit
        |
        | exact structural, timing, framing, and ordering refinement
        v
pure streaming fixed-point FFT
        |
        | exact layout correspondence
        v
pure fixed-point butterfly network
        |
        | decoding and numerical error bound
        v
exact complex butterfly network
        |
        | Cooley--Tukey and indexing theorems
        v
Mathlib ZMod.dft
```

Only the fixed-point-to-complex step is approximate. Hardware refinement,
latency, framing, indexing, and ordering are exact.

For every valid marked input frame, the public end-to-end theorem gives the
exact output latency and natural output ordering and bounds each decoded
hardware result against Mathlib's unnormalized, negative-exponent complex DFT.
Its premises state the input interpretation, certified twiddle approximation,
and the no-overflow conditions needed to rule out wrapping.

The formal hardware boundary is Silean's `ModuleStructure` semantics. FIRRTL
and SystemVerilog emission are executable validation paths; the renderer and
downstream tools are not yet proved semantics-preserving.

## Streaming architecture

The concrete top level is:

```text
InitialReorder
    -> UnrolledFFTNetwork
    -> FFTStageChain
    -> FinalReorder
```

`InitialReorder` performs global input bit reversal. The unrolled prefix
processes the layers whose operands arrive in the same packed cycle.
`FFTStageChain` implements the remaining rolled layers with explicit shift
registers, twiddle ROMs, and butterflies. `FinalReorder` converts the final
streamed layout to natural frequency order.

`i_first` marks the first cycle of a candidate input frame and `o_first` marks
the corresponding output frame. The contract applies when no second `i_first`
arrives during that input frame. An early marker invalidates the interrupted
frame and may begin another candidate frame. The interface does not require a
reset.

## Arithmetic and accuracy

Exact vectors use `Fin (2 ^ depth) -> Complex` in natural frequency order.
The exact recursive transform uses decimation in time: it splits even and odd
inputs, writes sums in the lower output half, writes differences in the upper
half, and requires no final permutation. The hardware-shaped layered network
instead performs one input bit reversal before ascending butterfly layers.

Fixed-point values are scaled integers. Width and fractional precision are
independent, wrapping is explicit, and representability and absence of
overflow are propositions rather than hidden assumptions. Complex
multiplication forms each real or imaginary numerator at full precision and
rounds once using nearest with ties to even.

For input magnitude bound `M_s`, input error bound `E_s`, twiddle error
`delta_s`, and local arithmetic allowance `R_s`, one layer establishes:

```text
M_(s+1) = 2 M_s
E_(s+1) = (2 + delta_s) E_s + M_s delta_s + R_s
```

With exact twiddles and constant `R`, this becomes
`E_s = 2^s E_0 + (2^s - 1) R`.

## Source guide

- `Exact/` defines the mathematical radix-2 and layered transforms and proves
  equality with Mathlib's DFT.
- `FixedPoint.lean` and `FixedPoint/` define scaled-integer arithmetic and its
  decoding, range, and rounding results.
- `Fixed/` defines the pure fixed-point FFT, twiddle certification,
  no-overflow conditions, and numerical error propagation.
- `Silean/` contains the concrete structural hardware, public contracts, and
  refinement proofs.
- `Silean/FFT.lean` is the public entry point for the complete streaming
  hierarchy and its correctness theorem.

Public contracts use natural Lean values and traces. Bit layouts, child state,
instance names, schedules, and wiring proofs remain internal to structural
implementations.

## Current status

The exact FFT, fixed-point model, numerical bound, arithmetic modules,
unrolled prefix, rolled stages, reorderers, complete streaming hierarchy, and
end-to-end hardware-to-DFT theorem are proved in Lean. The hierarchy is closed:
its implementation contains no unresolved children.

The remaining work is generated-RTL validation:

1. Select a modest concrete transform size, samples-per-cycle count, numeric
   format, and pipeline placement.
2. Inspect the closed hierarchy and emitted arithmetic widths.
3. Emit FIRRTL and lower it to SystemVerilog.
4. Simulate deterministic complete frames and check values, ordering, marker
   timing, latency, and back-to-back throughput.
5. Inspect shift-register construction and multiplier lowering.

Later numerical optimizations may introduce stage-dependent fractional-bit
trimming or rescaling. Ready/valid backpressure, gaps within frames, RAM-backed
delay storage, floating point, and external-module substitution are outside
the current design.
