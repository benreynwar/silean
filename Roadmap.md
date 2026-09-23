# Silean roadmap

This is the project-level roadmap. It records current direction and remaining
work, not the history of every intermediate design. The detailed FFT plan is
in [`HTFFT/Plan.md`](HTFFT/Plan.md).

## Destination

Silean explores writing recognizable structural hardware and useful
correctness proofs in the same Lean program. A concrete `ModuleStructure`
denotes simultaneous structural equations. Independent proofs establish that
those equations have one result and that the result satisfies a natural
behavioral specification. The same structure is used for FIRRTL emission.

The current main client is HTFFT: a streaming fixed-point FFT with an exact
hardware-refinement proof and a numerical error bound against Mathlib's DFT.
PicoRV remains a second, currently paused client for eventual equivalence and
architectural-refinement work.

## Established foundation

The framework currently supports:

- recursive bit, vector, and named-tuple signal shapes;
- finite symbolic labels and dependently typed signal maps;
- primitive, splitter, combiner, and composite structures;
- total typed wiring and recursively owned concrete hierarchy;
- simultaneous structural equations and finite execution;
- contract-independent schedules proving existence and uniqueness;
- exact cycle contracts for local one-cycle behavior;
- state-free boundary traces with fixed- and framed-latency relations;
- unresolved immediate children in a `ModuleBody` for top-down development;
- synchronized body traces and a bridge from concrete composite execution;
- authoring macros for boundaries, structures, contracts, and proof schedules;
- ordinary Lean construction for recursive or generated families; and
- direct FIRRTL generation with CIRCT, Verilator, and cocotb regression.

The reusable hardware library includes registers, optional and required shift
registers, muxes, logic, counters, adapters, register banks, FIFOs, structural
ROMs, fixed-width rounding, and signed and unsigned arithmetic with unequal
operand widths. Certified pipelined multiplication and butterfly modules that
encode HTFFT-specific arithmetic policy remain under `HTFFT/`.

## Architectural commitments

These decisions should change only in response to concrete implementation
experience:

- `ModuleStructure` contains executable structural hardware, not behavioral
  contracts, evaluation schedules, or unresolved blackboxes.
- Structure denotes simultaneous equations. Schedules are proof witnesses for
  existence and uniqueness, not circuit meaning.
- Structural certification is independent of contract style.
- Public contracts use natural Lean and do not expose child instances, wiring,
  physical state trees, emitted names, or proof bookkeeping.
- Exact cycle, fixed-latency, framed, reset, FIFO, and custom relational
  contracts coexist; no single contract type is privileged.
- Top-down proofs use `ModuleBody` traces and explicit child predicates.
  Replacing an unresolved child with a concrete design preserves the body and
  its conditional proof.
- Emitted names are metadata. Typed endpoints and preserved structural IDs are
  semantic identity.
- `module_design` or an ordinary Lean structural definition is authoritative.
  An additional human-facing circuit description is justified only when it
  materially improves readability.
- Helpers should capture repeated construction or proof patterns, not conceal
  one awkward client proof.
- When a proof is unexpectedly difficult, inspect the abstraction boundary
  before adding module-specific machinery.

## Current priority: complete HTFFT

The following foundation is complete:

- equality of the exact radix-2 network with Mathlib's `ZMod.dft`;
- a hardware-shaped exact network with explicit ordering;
- a pure fixed-point network with no-overflow conditions and global error
  propagation;
- certified twiddle generation and a closed eight-point accuracy example;
- certified arithmetic, complex multiplication, butterfly, and unrolled FFT
  hardware;
- natural framed contracts for the streaming top level and its immediate
  children;
- conditional top-level and rolled-stage-chain proofs over unresolved
  children; and
- the generic pure scheduling theorem for one rolled `FFTStage`, including
  rephasing, delay-line independence, operand pairing, twiddle addressing,
  marker timing, and complete-frame correctness.

The next work is the concrete generic `FFTStage`:

1. Build its permanent hierarchy from explicit shift registers, phase control,
   muxes, the certified twiddle ROM, and certified butterflies.
2. State its exact structural latency and required alignment paths.
3. Prove concrete execution refines the completed pure stage schedule using
   only public child interfaces.
4. Discharge the existing framed `FFTStage` contract without changing that
   contract to fit the implementation.
5. Inspect, emit, and simulate at least one closed configuration.

After the stage:

1. implement and certify the initial and final shift-register packet
   reorderers against their existing framed permutation contracts;
2. replace the remaining unresolved children and close the complete hierarchy;
3. emit and simulate the complete streaming FFT; and
4. compose exact hardware refinement, ordering, no-overflow, numerical error,
   and the exact DFT theorem into the final hardware-to-DFT bound.

Configuration choices, the frame protocol, proof layering, deferred precision
policies, and milestone details remain in [`HTFFT/Plan.md`](HTFFT/Plan.md).

## Framework work driven by HTFFT

Framework changes should be made when the concrete stage or reorderer proofs
demonstrate a reusable need. Likely areas are:

- small trace-composition laws for synchronized fixed-latency children;
- concise structural schedules for regular indexed families;
- reusable reasoning about shift-register networks; and
- clearer diagnostics where dependent wiring or schedule elaboration fails.

Do not add RAM inference, external-module semantics, automatic blackbox
obligation collection, or another contract hierarchy speculatively. The first
HTFFT target deliberately uses explicit shift registers.

A separate repository-wide proof-trust review remains required. Production
proofs must be kernel-checkable and free of `sorry`, project axioms,
`native_decide`, and unsafe shortcuts. Tests and executable checks may use
appropriate evaluation mechanisms.

## Paused PicoRV direction

PicoRV currently has a concrete configured hierarchy with component
certifications and top-level structural existence and uniqueness. It is not the
current priority and may temporarily lag framework changes.

When resumed, its two distinct goals are:

```text
configured upstream picorv32.v
        equivalent to
certified Silean PicoRV structure
        refines
clean RV32I execution
```

The detailed proof boundary and staged instruction plan remain in
[`docs/picorv/PicoRV32Plan.md`](docs/picorv/PicoRV32Plan.md). Source
equivalence, architectural safety, and progress under memory fairness must stay
separate theorems.

## Longer-term work

- Prove semantics preservation from the supported closed `ModuleStructure`
  subset to emitted FIRRTL, or introduce a smaller checked backend boundary.
- Add temporal contract forms only when a concrete design requires them.
- Consider memory-array structural primitives only when a target actually
  needs them.
- Treat intentional external RTL as an emission substitution for a verified
  Silean reference design, rather than giving it unconstrained semantics.

## Completion standard

A feature is complete only when:

- its public boundary and natural contract are clear;
- its simultaneous structural equations are shown non-vacuous and unique;
- its correctness theorem uses public child interfaces;
- documentation states the actual formal boundary;
- production proofs are kernel-checkable and placeholder-free; and
- proportionate Lean and generated-hardware regressions pass.
