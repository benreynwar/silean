import PicoRV.Decoder.DecoderCaptureStage
import PicoRV.Decoder.DecoderImmediate
import PicoRV.Decoder.DecoderInstructionFields
import PicoRV.Decoder.DecoderInstructionMatchGate
import PicoRV.Decoder.DecoderInstructionMatch
import PicoRV.Decoder.DecoderInstructionSummary
import PicoRV.Decoder.DecoderResolveStage

assert_not_imported PicoRV.Decoder.Internal.DecoderCaptureStageStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderImmediateStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderInstructionFieldsStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderInstructionMatchGateStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderInstructionMatchStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderInstructionSummaryStructure
assert_not_imported PicoRV.Decoder.Internal.DecoderResolveStageStructure

namespace PicoRVTests.DecoderComponentAuthoring

#check PicoRV.Decoder.CaptureStage.cycleContract
#check PicoRV.Decoder.Immediate.cycleContract
#check PicoRV.Decoder.InstructionFields.cycleContract
#check PicoRV.Decoder.InstructionMatch.MatchGate.cycleContract
#check PicoRV.Decoder.InstructionMatch.cycleContract
#check PicoRV.Decoder.InstructionSummary.cycleContract
#check PicoRV.Decoder.ResolveStage.cycleContract

#check PicoRV.Decoder.CaptureStage.description.ImplementsCycleContract
  PicoRV.Decoder.CaptureStage.cycleContract
  PicoRV.Decoder.CaptureStage.Naming.ports

#check PicoRV.Decoder.Immediate.description.ImplementsCycleContract
  PicoRV.Decoder.Immediate.cycleContract
  PicoRV.Decoder.Immediate.Naming.ports

#check PicoRV.Decoder.InstructionMatch.MatchGate.description.ImplementsCycleContract
  PicoRV.Decoder.InstructionMatch.MatchGate.cycleContract
  PicoRV.Decoder.InstructionMatch.MatchGate.Naming.ports

end PicoRVTests.DecoderComponentAuthoring
