import Silean.Contracts.SignalExpectation
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Contracts.Cycle.CycleImplementation
import Silean.Contracts.Cycle.CycleTrace
import Silean.Contracts.Cycle.CycleLayerSchedule
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Reset.ResetContract
import Silean.Contracts.Reset.ResetImplementation
import Silean.Contracts.Fifo.FifoContract
import Silean.Contracts.Fifo.FifoPortContract
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Contracts.Fifo.FifoCycleRefinement

/-! # Behavioral contracts and certification

This aggregate exports the specification layers used to state and prove module
behavior. Cycle contracts give exact one-cycle equations; reset contracts
describe synchronization and behavior across traces; FIFO contracts express
latency-independent valid/ready queue behavior. The cycle certification
machinery connects independent structural solutions to contracts and proves
existence, uniqueness, and behavioral refinement compositionally.
-/
