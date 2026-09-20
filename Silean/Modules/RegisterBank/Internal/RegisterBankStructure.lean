import Silean.Authoring.ModuleDesign
import Silean.Modules.BinaryToOneHot.BinaryToOneHotDerived
import Silean.Modules.CombMuxTree.CombMuxTreeDerived
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

/-! Generated indexed hierarchy and naming for the register bank. -/

namespace Silean.Modules.RegisterBank

open Silean

def entryCombiner (element : SignalType)
    (addressWidth : Nat) : Composition.SignalCombiner :=
  .vector (entryCount addressWidth) element

end Silean.Modules.RegisterBank

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design RegisterBank (element : SignalType) (addressWidth : Nat)
    (readCount : Nat) where
  boundary (RegisterBank.ports element addressWidth readCount)
    (naming := RegisterBank.Naming.ports element addressWidth readCount)
  instances {
    decoder := BinaryToOneHot.design addressWidth,
    decodeSplit :=
      Naming.SignalAdapter.splitterDesign
        (Composition.SignalSplitter.vector
          (RegisterBank.entryCount addressWidth) .bit),
    gate (index : Fin (RegisterBank.entryCount addressWidth) in
        Enumeration.fin (RegisterBank.entryCount addressWidth))
      (name := s!"write_gate_{index.val}") := Primitives.andDesign,
    storage (index : Fin (RegisterBank.entryCount addressWidth) in
        Enumeration.fin (RegisterBank.entryCount addressWidth))
      (name := s!"entry_{index.val}") := EnabledRegister.design element,
    combine :=
      Naming.SignalAdapter.combinerDesign
        (RegisterBank.entryCombiner element addressWidth),
    readMux (port : Fin readCount in Enumeration.fin readCount)
      (name := s!"read_{port.val}_mux") :=
        CombMuxTree.design element addressWidth }
  wiring {
    outputs {
      .readValue port := readMux(port)[.result] }
    instance (.decoder) {
      .value := input.writeAddress }
    instance (.decodeSplit) {
      .value := decoder.result }
    instance (.gate index) {
      .left := input.writeEnable,
      .right := decodeSplit[index] }
    instance (.storage index) {
      .data := input.writeValue,
      .enable := gate(index)[.output] }
    instance (.combine) {
      index := storage(index)[.q] }
    instance (.readMux port) {
      .values := combine.value,
      .index := input[.readAddress port] }
  }

end Silean.Modules

namespace Silean.Modules.RegisterBank.Naming

open Silean Silean.Naming

def namingWith (element : SignalType) (addressWidth readCount : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth readCount) := by
  unfold Modules.RegisterBank.moduleStructure
  exact .composite ⟨"RegisterBank", "",
      [.signalType element, .natural addressWidth, .natural readCount]⟩
    (portsWithNaming element addressWidth readCount elementNaming)
    (instanceNames element addressWidth readCount)
    (fun
      | .decoder => BinaryToOneHot.Naming.naming addressWidth
      | .decodeSplit => Silean.Naming.SignalAdapter.splitter
          (.vector (Modules.RegisterBank.entryCount addressWidth) .bit)
      | .gate _ => Silean.Naming.Primitive.and
      | .storage _ => EnabledRegister.namingWith element elementNaming
      | .combine =>
          Silean.Naming.SignalAdapter.combinerWithNaming
            (Composition.SignalSplitter.vector
              (Modules.RegisterBank.entryCount addressWidth) element).combiner
            (.vector elementNaming)
      | .readMux _ =>
          CombMuxTree.Naming.namingWith element addressWidth elementNaming)

def naming (element : SignalType) (addressWidth readCount : Nat) :
    ModuleNaming (Modules.RegisterBank.moduleStructure element addressWidth readCount) :=
  namingWith element addressWidth readCount (.positional element)

end Silean.Modules.RegisterBank.Naming
