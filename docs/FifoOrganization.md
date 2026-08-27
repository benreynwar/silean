# FIFO organization review

This review records the current FIFO responsibilities and why each retained
layer exists. It describes the current design, not compatibility history.

## Responsibility map

| Source | Owns | Does not own |
| --- | --- | --- |
| `Modules/FifoInterface.lean` | Generic ready/valid/data port labels, typed maps, ports, and contract rule names | Storage, hierarchy, execution, or proofs |
| `Modules/OneEntryFifo.lean` | One-entry structural hierarchy, its cycle contract, certification, public contract equations, and naming | Finite execution or trace properties |
| `Modules/FifoCycleBehavior.lean` | Forward/ready/next-state behavior, conversion to a cycle contract, serial behavior composition, and certified behavior packaging | Structural schedules or finite traces |
| `Modules/SerialFifo.lean` | Two-child structural wiring and certification against serial cycle behavior | A separate evaluator |
| `Modules/Fifo.lean` | Positive-depth recursive structure, behavior, contract, certification, and naming | Conservation/capacity proofs |
| `Modules/FifoExecution.lean` | The single generic interpretation of FIFO cycle behavior and its serial step decomposition | Module hierarchy or logical FIFO contents |
| `Modules/OneEntryFifoProperties.lean` | One-entry logical contents, conservation, capacity, and ready-stall proofs | A second implementation of cycle evaluation |
| `Modules/FifoProperties.lean` | Generic certified views, serial property composition, and positive-depth capacity/latency results | Structural proof construction |
| `Contracts/NoResetFifo*.lean` | Implementation-independent traces, execution laws, views, and serial theorems | Knowledge of Silean module instances |

The intended progression is:

`interface → cycle behavior/contract → certified structure → execution → properties`

Structure and contract remain independent descriptions. Certification connects
them. Execution interprets the already-certified contract; it is not another
structural semantics and is not stored in `ModuleStructure`.

## Retained abstractions

- `Fifo.CycleBehavior` is useful because serial composition can be stated once
  over forward, ready, and next-state functions and then converted to ordinary
  `ModuleCycleContract` rules.
- `Fifo.CertifiedCycleBehavior` is the typed child interface needed by
  structural serial composition: it carries the public behavior, exact
  structure, and their certification without exposing how the proof was built.
- `Fifo.Execution` is useful because all FIFO shapes execute through one generic
  `ModuleCycleContract.evaluate` bridge. One-entry and positive-depth FIFOs do
  not define competing evaluators.
- `NoResetFifo.View` packages only the logical contents interpretation and its
  capacity/ready-latency bounds. Its serial laws are independent of hardware
  hierarchy and can be reused by other FIFO implementations.

## Removed or hidden details

- The port and rule labels formerly owned by `OneEntryFifo` are now the generic
  FIFO interface used consistently by one-entry, serial, and positive-depth
  modules.
- The duplicated one-entry evaluator and its duplicate output-evaluation lemmas
  were removed in favor of `Fifo.Execution`.
- `Temporal` was removed from files and namespaces. `CycleBehavior`,
  `Execution`, and `Properties` state the actual responsibility; “temporal” was
  too broad to distinguish these layers.
- The hand-written two-stage execution regression was removed. It duplicated
  the production serial execution constructor; depth checks now cover the
  reusable path.
- Concrete child occurrences, wiring contexts, schedules, proposal builders,
  state-correspondence witnesses, and certification constructors in
  `OneEntryFifo` and `SerialFifo` are private. Consumers use module structures,
  contracts, certifications, and public behavioral theorems.
- Positive-depth recursion helpers and recursive view builders are private when
  they do not cross a responsibility boundary. The public depth API uses actual
  positive depth rather than the internal “additional entries” index.

## Remaining public surface

The useful module-facing entry points are the FIFO ports, `moduleStructure`,
`cycleBehavior`, `cycleContract`, `certification`/`certified`, module naming,
generic execution, and proven properties such as exact capacity and ready
propagation latency. Public rule equations describe contracts rather than child
implementation details.

This organization keeps FIRRTL generation straightforward: it consumes the
computable `ModuleStructure` and naming metadata directly. None of the behavior,
execution, view, or property layers is required to render the circuit.
