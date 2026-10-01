import Silean.FIRRTL.Emit
import PicoRV.Decoder.DecoderCaptureStageDerived

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-decoder-capture" args
    (Silean.FIRRTL.renderCircuit
      PicoRV.Decoder.CaptureStage.naming)
