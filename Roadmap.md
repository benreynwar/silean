# Silean roadmap

## Destination

Silean is an experiment in writing structural hardware and useful correctness
proofs in the same Lean program. The design should remain close enough to a
conventional hierarchical HDL that hardware engineers can recognize ports,
instances, wiring, state, and reusable modules.

A structure denotes simultaneous equations. Proofs establish that those
equations have one result and that every result satisfies an independently
written behavioral contract. FIRRTL is emitted directly from the same
structure.

The long-term application is a small RV32I processor based on a fixed,
source-faithful PicoRV32 configuration. Its public theorem should concern
observable memory-mapped-I/O and termination or trap behavior, with stronger
memory-transaction correspondence available as a supporting property.

## Established capabilities

The repository currently has:

- recursive bit, vector, and named-tuple signal shapes;
- finite symbolic labels and dependently typed signal maps;
- total same-shaped wiring and recursively owned module structures;
- primitive, splitter, combiner, composite, and explicit blackbox leaves;
- simultaneous structural equations expressed by one recursive `HierStep`;
- finite structural execution and an executable no-blackbox check;
- exact cycle contracts with independent behavioral state;
- contract-only proof schedules establishing existence and complete
  hierarchy-wide uniqueness;
- concise authoring declarations for ordinary fixed modules, with recursive
  and generated designs deliberately retaining ordinary Lean;
- a reader-facing `Foo.lean` / `FooTheorems.lean` interface and private
  `Internal/` structure and verification files where that separation helps;
- reset-synchronized trace contracts with ternary output expectations;
- latency-independent valid/ready FIFO contracts;
- direct FIRRTL generation, CIRCT/Verilator lowering, and cocotb regression;
- reusable registers, muxes, logic, arithmetic, adapters, counters, register
  banks, and FIFO implementations; and
- a public proof that the pointer FIFO satisfies its bounded abstract FIFO
  contract after reset.

The configured PicoRV32 hierarchy is fully structural and recursively
blackbox-free. Decoder, memory, datapath, control, register file, and their
children have closed certified structures. The top-level hierarchy has
existence and uniqueness proofs. It does not yet have the processor-level
architectural refinement theorem described below.

## Current constraints

- Signal semantics are two-state Boolean semantics.
- A single global clock is implicit throughout the hierarchy.
- Reset is synchronous and module-specific.
- The formal correctness boundary ends at `ModuleStructure`; FIRRTL and
  SystemVerilog are regression-tested but not proved semantics-preserving.
- Blackboxes are explicit assumptions and must be absent from a closed design.
- Contract state should be natural for specification and need not reproduce
  the structural state tree.
- High-level modules need not expose exact cycle contracts when a temporal or
  observational contract is more appropriate.
- New helpers should capture genuinely repeated proof or construction
  patterns, not special cases for one module.

## Near-term work

### Define and prove processor-level observation

The next processor milestone extends the verification stages in
[`docs/PicoRV32Plan.md`](docs/PicoRV32Plan.md):

1. define the external memory environment and identify the memory-mapped-I/O
   address region outside the processor core;
2. define observable completed bus transactions, retirement, trap, and
   termination without adding emitted RVFI hardware;
3. relate reachable PicoRV contract state to a committed RV32I state plus
   explicit in-flight instruction and memory-operation information;
4. prove one complete ADDI slice, including memory stalls and stuttering
   implementation cycles;
5. extend the argument to loads and stores before generalizing across the
   instruction set; and
6. derive the public I/O-trace theorem, retaining ordinary-memory
   correspondence as a stronger supporting property where required.

The architectural model should remain behind a narrow adapter. Safety and
progress are separate: the trace refinement must be accompanied eventually by
an explicit responsiveness or fairness assumption for memory.

### Keep proof interfaces small

Schedule derivation, child-contract matching, and wiring normalization already
remove much of the mechanical certification work. Continue reducing repeated
proof plumbing only when a helper improves both a module's public theorem
interface and real downstream proofs. Do not hide module bodies, wiring, state
correspondence, module-specific reasoning, or the final behavioral argument
merely to reduce line count.

### Revisit elaboration performance

Some of the larger decoder and top-level checks remain expensive enough to
interrupt interactive work. Profile those files before changing proof APIs,
and prefer improvements to shared normalization or elaboration behavior over
module-specific shortcuts.

## Longer-term work

- Prove a semantics-preservation bridge from the supported closed
  `ModuleStructure` subset to emitted FIRRTL, or validate a smaller checked
  backend representation if that gives a clearer theorem.
- Add contract forms for other useful temporal abstractions as real designs
  demand them.
- Explore whether memory arrays deserve a structural primitive only when a
  design requires one; current plans do not assume it.

## Completion standards

A feature is complete only when its public structure and natural contract are
clear, the relevant existence or non-vacuity condition is proved, reusable
proofs do not depend on hidden child implementations, documentation states the
actual correctness boundary, and the appropriate Lean and generated-hardware
regressions pass.
