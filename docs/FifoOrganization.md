# FIFO organization

There are two deliberately separate FIFO families. `Fifo` is the primary
resettable address-plus-wrap implementation. `NoResetFifo` and
`SerialDepthFifo` provide the fall-through serial-composition model used by
the existing trace and capacity proofs.

## Responsibility map

| Source | Owns | Does not own |
| --- | --- | --- |
| `Modules/FifoInterface.lean` | Primary FIFO ready/valid/data/reset port vocabulary | Structure, contracts, or proofs |
| `Modules/Fifo.lean` | Primary resettable FIFO contract, exact four-child pointer/bank hierarchy, certification, public cycle laws, and naming | Trace execution or a memory backend |
| `Modules/FifoResetContract.lean` | Natural `List T` reset-synchronized contract, ternary observations, queue transfers, capacity, and trace laws | FIFO structure, cycle contract, or reset certification |
| `Modules/FifoResetCertified.lean` | Direct trace refinement from the canonical structure to the List-based reset contract | A generic cycle-to-reset bridge or public state relation |
| `Modules/FifoProperties.lean` | Logical occupancy and queue contents, reachable invariant, reset-aware execution, cycle correctness, and arbitrary-trace FIFO theorems | Structural children or certification internals |
| `Modules/NoResetFifoInterface.lean` | No-reset fall-through ready/valid/data interface and rule names | Storage, hierarchy, execution, or proofs |
| `Modules/OneEntryFifoControl.lean` | Combinational update/ready control used only by OneEntryFifo | Generic pointer FIFO control |
| `Modules/OneEntryFifo.lean` | One-entry structural hierarchy, its cycle contract, certification, public contract equations, and naming | Finite execution or trace properties |
| `Modules/NoResetFifoCycleBehavior.lean` | Forward/ready/next-state behavior, conversion to a cycle contract, serial behavior composition, and certified behavior packaging | Structural schedules or finite traces |
| `Modules/SerialFifo.lean` | Two-child structural wiring and certification against serial cycle behavior | A separate evaluator |
| `Modules/SerialDepthFifo.lean` | Positive-depth recursive structure, behavior, contract, certification, and naming | Conservation/capacity proofs |
| `Modules/NoResetFifoExecution.lean` | The single generic interpretation of FIFO cycle behavior and its serial step decomposition | Module hierarchy or logical FIFO contents |
| `Modules/OneEntryFifoProperties.lean` | One-entry logical contents, conservation, capacity, and ready-stall proofs | A second implementation of cycle evaluation |
| `Modules/SerialDepthFifoProperties.lean` | Generic certified views, serial property composition, and positive-depth capacity/latency results | Structural proof construction |
| `Contracts/NoResetFifo*.lean` | Implementation-independent no-reset traces, execution laws, views, and serial theorems | Knowledge of Silean module instances |
| `Contracts/ResetFifo.lean` | Reset-aware accepted transfers, queue-step semantics, finite transitions, and generic trace lifting | Knowledge of Silean modules or storage layout |
| `Foundation/Execution.lean` | Deterministic step results and finite folding over an input list | FIFO transfers, reset, queue contents, or module structure |

The no-reset serial family progresses as:

`interface → cycle behavior/contract → certified structure → execution → properties`

Structure and contract remain independent descriptions. Certification connects
them. Execution interprets the already-certified contract; it is not another
structural semantics and is not stored in `ModuleStructure`.

The reset certification consumes the existing cycle certificate only as a
private proof technique. Its trace induction keeps cycle/structural
correspondence before reset, establishes empty bounded logical contents on a
reset edge, and preserves that alignment on ordinary edges. The exported
`Fifo.resetCertified` contains only structure, reset contract, and trace
refinement.

## Retained abstractions

- `NoResetFifo.CycleBehavior` is useful because serial composition can be stated once
  over forward, ready, and next-state functions and then converted to ordinary
  `ModuleCycleContract` rules.
- `NoResetFifo.CertifiedCycleBehavior` is the typed child interface needed by
  structural serial composition: it carries the public behavior, exact
  structure, and their certification without exposing how the proof was built.
- `NoResetFifo.Execution` is useful because all FIFO shapes execute through one generic
  `ModuleCycleContract.evaluate` bridge. One-entry and positive-depth FIFOs do
  not define competing evaluators.
- `NoResetFifo.View` packages only the logical contents interpretation and its
  capacity/ready-latency bounds. Its serial laws are independent of hardware
  hierarchy and can be reused by other FIFO implementations.

## Public surface

The primary FIFO exposes its ports, logical pointer/entry state, natural cycle
contract, contract-level laws, computable `moduleStructure`, `certified`
bundle, and naming. Synchronous reset affects pointer next state; current-cycle
handshakes and an accepted bank write are determined from pre-edge state. The
following state is empty without clearing storage.

`Fifo.Properties` interprets a state satisfying its occupancy `Invariant` as a
logical queue. Its
occupancy is the circular distance between the extended pointers, and its
contents are the corresponding entries beginning at the read address. The
reachable invariant bounds that distance by `2 ^ addressWidth`. Public proofs
show that empty/full agree with occupancy zero/capacity, each ordinary cycle
obeys queue conservation (including simultaneous transfers and wraparound),
reset clears the logical queue, the invariant is preserved, and every finite
execution satisfies the reset-aware transition relation. For a reset-free
trace, accepted outputs are a prefix of accepted inputs when starting empty,
so values cannot be lost, duplicated, or reordered. These proofs use only the
public cycle contract, never the FIFO's structural children.

The finite runner is shared with the no-reset FIFO family, but only at the
mechanical level: it folds a deterministic step and records observations.
FIFO-specific inputs, cycles, reset semantics, transition relations,
conservation, and ordering remain in their respective contract namespaces.

The no-reset family exposes its interface, cycle behavior, certified serial
structures, generic execution, and proven capacity/ready-latency properties.
Both families keep child identities, schedules, proposal construction,
state-correspondence witnesses, and refinement constructors private.

This organization keeps FIRRTL generation straightforward: it consumes the
computable `ModuleStructure` and naming metadata directly. None of the behavior,
execution, view, or property layers is required to render the circuit.
