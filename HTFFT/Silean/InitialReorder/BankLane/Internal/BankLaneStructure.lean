import HTFFT.Silean.InitialReorder.BankLane.BankLane
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterDerived
import Silean.Modules.Register.RegisterDerived
import Silean.Modules.RegisterBank.RegisterBankDerived

namespace HTFFT.Silean
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design InitialReorder.BankLane (depth : Nat)
    (name := "InitialReorderBankLane")
    (configuration : Configuration depth)
    (specialization := [.natural depth, .natural configuration.laneDepth,
      .signalType (InitialReorder.BankLane.sampleType configuration)]) where
  boundary (InitialReorder.BankLane.ports configuration)
    (naming := InitialReorder.BankLane.Naming.ports configuration)
  instances {
    trueSource := Constant.design .bit true,
    payloadUnpack := NamedTupleSplitter.design
      (InitialReorder.Lane.payloadMap configuration),
    bank := RegisterBank.design
      (InitialReorder.BankLane.sampleType configuration)
      (InitialReorder.addressWidth configuration) 1,
    outputRegister := Register.design
      (InitialReorder.BankLane.sampleType configuration) }
  wiring {
    outputs {
      .o_data := outputRegister.output }
    instance (.trueSource) {}
    instance (.payloadUnpack) {
      .value := input.i_writePayload }
    instance (.bank) {
      .writeEnable := trueSource.output,
      .writeAddress := payloadUnpack.address,
      .writeValue := payloadUnpack.data,
      .readAddress 0 := input.i_readAddress }
    instance (.outputRegister) {
      .input := bank[.readValue 0] }
  }

end HTFFT.Silean
