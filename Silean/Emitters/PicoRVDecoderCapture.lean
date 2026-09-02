import Silean.FIRRTL.Emit
import Silean.Examples.PicoRV.Decoder.DecoderCaptureStage

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-decoder-capture" args
    (Silean.FIRRTL.renderClosedCircuit
      Silean.Examples.PicoRV.Decoder.CaptureStage.Naming.naming)
