# FIFO organization

All FIFO implementations use `Interfaces/FifoPorts.lean`. Its
`Silean.Interfaces.Fifo` namespace owns the
canonical input/output labels and defines the two boundary interfaces:
`Interfaces.ValidReadySink` for traffic entering the FIFO and
`Interfaces.ValidReadySource` for
traffic leaving it. Interfaces identify and interpret ports; they do not state
FIFO ordering or expose implementation state.

## Public behavioral contract

`Contracts/Fifo/FifoContract.lean` defines the latency-independent
`Contracts.Fifo.FifoContract`. It owns:

- one valid/ready sink and one valid/ready source with the same payload shape;
- a synchronous reset input;
- a capacity;
- boundary input and output transfers derived from the interfaces; and
- a reset-synchronized finite-trace relation over a logical bounded queue.

Behavior is unconstrained before the first reset and on each reset cycle. The
state following reset is the empty logical queue. On ordinary synchronized
cycles the queue equation is

`oldQueue ++ acceptedInput = acceptedOutput ++ nextQueue`.

This equation permits fall-through and registered implementations without
constraining latency or internal state. Generic trace laws prove conservation
over reset-free synchronized suffixes, output ordering from an empty queue,
and the capacity bound on every synchronized logical queue.

`Contracts.Fifo.FifoCertified` pairs a structure with this contract. Its `hasSolution` field
requires a structural result for every structural state and cycle input, so an
inconsistent structure cannot satisfy refinement vacuously. Its implementation
field says every finite structural execution is accepted by the contract.

## Proof bridge

`Contracts/Fifo/FifoCycleRefinement.lean` defines the private-proof adapter used
by current implementations. A `Contracts.Fifo.FifoCycleRefinement` supplies an invariant and a logical
queue interpretation for an already cycle-certified module. It proves reset
establishment, ordinary-cycle queue preservation, and the capacity bound. The
adapter then performs the trace induction and produces a public
`Contracts.Fifo.FifoCertified`; neither the invariant nor the state interpretation appears in
that result.

## Implementations

| Source | Responsibility |
| --- | --- |
| `Modules/OneEntryFifo/OneEntryFifo.lean` | One-entry structure, exact cycle contract, certification, and naming |
| `Modules/OneEntryFifo/OneEntryFifoControl.lean` | Private combinational control child used only by OneEntryFifo |
| `Modules/OneEntryFifo/OneEntryFifoCycleBehavior.lean` | Natural exact cycle behavior for the one-entry implementation |
| `Modules/OneEntryFifo/OneEntryFifoCertified.lean` | Capacity-one logical queue refinement and public FIFO certification |
| `Composition/FifoSerialComposition.lean` | Generic two-child serial structure and cycle certification |
| `Composition/FifoSerialRefinement.lean` | Generic composition of two child FIFO refinements; downstream contents precede upstream contents and the internal transfer cancels |
| `Naming/FifoSerialNaming.lean` | Presentation names for the generic serial hierarchy |
| `Modules/SerialDepthFifo/SerialDepthFifo.lean` | Recursive positive-depth concrete structure, exact cycle contract, certification, and naming |
| `Modules/SerialDepthFifo/SerialDepthFifoCertified.lean` | Recursive FIFO certification with capacity equal to depth |
| `Modules/Fifo/Fifo.lean` | Pointer/register-bank structure and exact cycle contract |
| `Modules/Fifo/FifoPointerControl.lean` | Private pointer interpretation and transfer-control child used by the FIFO built from a register bank and pointers |
| `Modules/Fifo/FifoProperties.lean` | Circular-buffer occupancy, logical contents, invariant, and one-cycle queue lemmas |
| `Modules/Fifo/FifoCertified.lean` | Pointer-FIFO refinement and public capacity-`2^addressWidth` FIFO certification |

The serial composition proof consumes only child cycle behaviors and FIFO
refinements. It does not inspect either child structure or the schedules used
to certify it. The pointer implementation uses its public cycle contract and
logical circular-buffer lemmas; it does not retain a separate FIFO evaluator
or trace-view API.

## Separation from generation

FIRRTL generation consumes only `ModuleStructure` and naming metadata. FIFO
contracts, logical queues, invariants, and proof adapters are not required to
render a circuit. Synchronous reset remains ordinary module wiring and state
behavior: current outputs are from the pre-edge state, while the following
logical FIFO state is empty.
