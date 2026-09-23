# Silean roadmap

## Destination

Silean is an experiment in writing structural hardware and useful correctness
proofs in the same Lean program. Designs should remain close enough to a
conventional hierarchical HDL that hardware engineers can recognize ports,
instances, wiring, state, and reusable modules.

A concrete `ModuleStructure` denotes simultaneous structural equations.
Proofs establish that those equations have a unique result and that the result
satisfies an independently written behavioral contract. FIRRTL is emitted from
the same structure.

The two substantial clients currently exercise different parts of the design:

- **HTFFT** develops a streaming fixed-point FFT with an exact structural proof
  and a numerical error bound against Mathlib's DFT.
- **PicoRV** targets a source-faithful configured PicoRV32 implementation and a
  public refinement theorem about architectural and memory-mapped-I/O behavior.

## Established capabilities

### Structural framework

- Recursive bit, vector, and named-tuple signal shapes.
- Finite symbolic labels and dependently typed signal maps.
- Primitive, splitter, combiner, and composite module structures.
- Total same-shaped wiring and recursively owned concrete hierarchies.
- Simultaneous structural equations through one recursive `HierStep`.
- Finite execution for concrete hierarchies.
- Contract-independent structural-rule schedules proving existence and
  hierarchy-wide uniqueness.
- Cycle contracts where exact one-cycle behavior is the natural interface.
- State-free boundary traces, fixed-latency and framed-latency relations, and
  composition laws for higher-level temporal contracts.
- `ModuleBody` outlines and synchronized body traces for top-down proofs over
  unresolved immediate children.
- A bridge from observed execution of a concrete composite to the same body
  trace and child projections used by its conditional proof.
- Concise authoring declarations for ordinary modules, with recursive and
  generated families written in ordinary Lean where that is clearer.
- Direct FIRRTL generation, CIRCT/Verilator lowering, and cocotb regression.

### Reusable hardware

The library includes registers, optional and required shift registers, muxes,
logic, counters, adapters, register banks, FIFOs, structural ROMs, and general
signed or unsigned arithmetic with unequal widths. Carry-aware primitives have
explicit names; ordinary `Add`, `Sub`, and `AddSub` expose natural integer
contracts. The pointer FIFO has a public proof against its bounded abstract FIFO
contract.

### Client foundations

HTFFT has a complete exact FFT/DFT theorem, pure fixed-point model and numerical
error propagation, certified twiddle tables, certified butterfly and unrolled
FFT hardware, natural streaming contracts, conditional top-level and
rolled-stage-chain proofs, and a generic pure rolled-stage schedule proof.
Current and remaining HTFFT work is tracked in
[`HTFFT/Plan.md`](HTFFT/Plan.md).

PicoRV has a concrete configured hierarchy with certified component structures
and top-level structural existence and uniqueness. Exact equivalence with the
selected upstream Verilog and architectural refinement to the clean `RV32I/`
model remain separate open proofs.

The repository keeps reusable framework code in `Silean/`, the clean
architecture in `RV32I/`, the processor client in `PicoRV/`, optional
generated-Sail validation in `SailBridge/`, and project-specific FFT work in
`HTFFT/`.

## Framework invariants

These choices are settled unless implementation experience reveals a concrete
problem:

- Emitted names are metadata, not semantic identity. Authoring descriptions
  preserve description-local structural IDs; an emitter may separately reject
  name collisions.
- `ModuleStructure` describes executable structural hardware. Unresolved
  children live in a `ModuleBody`, not in a fake executable blackbox with
  invented or unconstrained semantics.
- A body proof receives ordinary explicit propositions about child traces.
  There is no required contract shape, automatic assumption collector, or
  proof-obligation descriptor.
- Replacing an unresolved child expression with a concrete design should retain
  the same generated ports, child interfaces, wiring, and body. A second
  outline-only authoring language is not needed.
- Structural existence and uniqueness are independent of behavioral contract
  style. Cycle contracts may contribute fine-grained dependency rules, while a
  conservative whole-module structural rule remains available.
- Contract state should be natural for the specification and need not reproduce
  the structural state tree.
- High-level modules need not use cycle contracts when a temporal, framed, or
  observational contract is more natural.
- Public contracts should be natural Lean. Instance names, emitted names,
  internal layouts, and proof bookkeeping should not leak into them.
- New helpers should capture repeated construction or proof patterns, not hide
  a one-off module argument.
- Client compatibility must not distort a cleaner reusable interface. Migrate a
  temporarily stale client separately when framework changes settle.

## Current constraints

- Signal semantics are two-state Boolean semantics.
- A single global clock is implicit throughout a hierarchy.
- Reset is synchronous and module-specific.
- The formal correctness boundary currently ends at `ModuleStructure`.
  Emitted FIRRTL and SystemVerilog are regression-tested but are not yet proved
  semantics-preserving.
- Intentional external RTL has no special semantic blackbox facility. If added,
  it should be verified against an ordinary Silean reference design and differ
  only at emission.

## Active work

### Complete the HTFFT hierarchy

The immediate project task is a concrete generic rolled `FFTStage`. Its pure
commutator-bank scheduling theorem is complete. The next refinement builds the
stage from explicit shift registers, phase control, a certified ROM, and
certified butterflies, then proves its public framed contract from child
interfaces.

After that, implement the initial and final shift-register packet reorderers,
replace the remaining unresolved children in the existing top-level bodies,
close and inspect the hierarchy, emit and simulate RTL, and compose the final
hardware-to-DFT accuracy theorem. The detailed order, protocol, proof boundary,
and open configuration choices live in
[`HTFFT/Plan.md`](HTFFT/Plan.md).

### Prove equivalence with the configured PicoRV Verilog

Connect the exact `picorv32.v` revision and configuration recorded in
[`docs/picorv/PicoRV32Plan.md`](docs/picorv/PicoRV32Plan.md) to the certified
Silean PicoRV structure. The existing scoped `mem_valid` comparison covers
only part of this goal. Define and review the exact equivalence statement and
proof boundary before extending the implementation.

### Refine the Silean PicoRV model to RV32I

The source-equivalence and architectural-refinement proofs are complementary:

```text
configured upstream picorv32.v
        equivalent to
certified Silean PicoRV structure
        refines
clean RV32I execution
```

Follow the stages in
[`docs/picorv/PicoRV32Plan.md`](docs/picorv/PicoRV32Plan.md):

1. define the external memory environment and memory-mapped-I/O region;
2. define observable completed bus transactions, retirement, trap, and
   termination without adding emitted RVFI hardware;
3. relate reachable PicoRV contract state to committed RV32I state plus
   explicit in-flight instruction and memory-operation information;
4. prove one complete ADDI slice, including memory stalls and stuttering;
5. extend to loads and stores before generalizing across the instruction set;
   and
6. derive the public I/O-trace theorem, retaining ordinary-memory
   correspondence where needed.

The clean `RV32I/` model is the direct architectural target. Its independent
agreement with generated Sail stays isolated in `SailBridge/`. Safety and
progress are separate; eventual progress needs an explicit responsiveness or
fairness assumption for memory.

### Improve reusable proof ergonomics when demanded by clients

- Keep child-contract matching, schedule derivation, and wiring normalization
  small without hiding module-specific reasoning.
- Add a balanced priority-mux tree with first-true-wins semantics and an
  explicit default when a real client is ready to use it.
- Profile expensive decoder and top-level elaboration before changing APIs;
  prefer shared normalization or elaboration improvements over local hacks.
- Perform a repository-wide proof-trust audit. Production proofs should avoid
  `native_decide`, `sorry`, project axioms, and unsafe shortcuts; tests and
  executable examples may use suitable evaluation mechanisms.

## Longer-term work

- Prove a semantics-preservation bridge from the supported closed
  `ModuleStructure` subset to emitted FIRRTL, or introduce a smaller checked
  backend representation if that yields a clearer theorem.
- Add other temporal contract forms only as concrete designs require them.
- Consider memory-array structural primitives only when a design needs them;
  the current HTFFT plan deliberately uses shift registers.
- Consider intentional external-module emission only with an ordinary verified
  Silean reference design.

## Completion standards

A feature is complete only when:

- its public structure and natural contract are clear;
- relevant existence, uniqueness, or non-vacuity conditions are proved;
- parent proofs depend on public child interfaces rather than hidden
  implementations;
- documentation states the actual correctness boundary;
- production proofs are kernel-checkable and free of placeholders; and
- the appropriate Lean and generated-hardware regressions pass.
