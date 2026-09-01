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
observable memory-mapped-I/O and termination/trap behavior, with stronger
memory-transaction correspondence available as a supporting property.

## Established capabilities

The repository currently has:

- recursive bit, vector, and named-tuple signal shapes;
- finite symbolic labels and dependently typed signal maps;
- total same-shaped wiring and recursively owned module structures;
- primitive, splitter, combiner, composite, and explicit blackbox leaves;
- simultaneous structural equations and finite structural execution;
- an executable, proved-correct recursive no-blackbox check;
- exact cycle contracts with independent behavioral state;
- contract-only proof schedules establishing structural existence and
  uniqueness without defining circuit meaning;
- parametric certified layers whose proofs use child contracts rather than
  child implementations;
- reset-synchronized trace contracts with ternary output expectations;
- latency-independent valid/ready FIFO contracts;
- direct FIRRTL generation, CIRCT/Verilator lowering, and cocotb regression;
- reusable generic registers, muxes, constants, equality, reductions,
  decoders, mux trees, register banks, counters, arithmetic, and bitwise logic;
- one-entry, serial-depth, and pointer/register-bank FIFOs; and
- a public proof that the pointer FIFO satisfies the bounded abstract FIFO
  contract after reset.

The most developed hardware example is the generic pointer FIFO. The largest
in-progress design is the configured PicoRV32 port: all five direct child
contracts and the typed top-level blackbox composition exist, while only the
ALU and register-file children currently have closed certified structures.

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

### Commit the cleanup checkpoint

The architectural cleanup has passed the full Lean and generated-hardware
regressions. Commit the accumulated changes before beginning another PicoRV
implementation. Split a large module later only when its private certification
detail demonstrably obscures the public ports, contract, structure, laws, and
naming; use a unique descriptive sibling filename when that becomes useful.

### Replace PicoRV32 child blackboxes

Implement and certify the remaining direct children against their existing
contracts, one source-faithful subsystem at a time:

1. decoder;
2. memory interface;
3. datapath, including iterative shifts and the already-certified ALU child;
4. control state machine; and
5. the top-level hierarchy with every blackbox replaced.

Child order may change when dependency evidence suggests a better route, but
all concrete structures must preserve the configured `picorv32.v` signal and
state ownership described in [docs/PicoRV32Plan.md](docs/PicoRV32Plan.md).

### Define and prove processor-level observation

Before claiming CPU correctness:

1. define the external memory environment and identify the memory-mapped-I/O
   address region outside the processor core;
2. define observable completed bus transactions, trap, and termination;
3. adapt the Sail-derived RV32I transition model in the sibling
   `sail-riscv32-lean` work into an instruction-retirement trace;
4. prove that the source-faithful microarchitectural execution refines that
   architectural trace; and
5. derive the weak public theorem about I/O traces, with ordinary-memory
   correspondence as a stronger supporting property where required.

This verification must not introduce RVFI hardware into the emitted design.
Any retirement record is a proof-level observation reconstructed from existing
state and bus behavior.

## Longer-term work

- Prove a semantics-preservation bridge from the supported closed
  `ModuleStructure` subset to emitted FIRRTL, or validate a smaller checked
  backend representation if that gives a clearer theorem.
- Add contract forms for other useful temporal abstractions as real designs
  demand them.
- Explore whether memory arrays deserve a structural primitive only when a
  design requires one; current plans do not assume it.
- Evaluate proof and elaboration performance as CPU structures replace
  blackboxes, keeping focused builds comfortably interactive.

## Completion standards

A feature is complete only when its public structure and natural contract are
clear, the relevant existence or non-vacuity condition is proved, reusable
proofs do not depend on hidden child implementations, documentation states the
actual correctness boundary, and the appropriate Lean and generated-hardware
regressions pass.
