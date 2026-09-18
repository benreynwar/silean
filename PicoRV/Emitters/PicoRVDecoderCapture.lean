import Silean.FIRRTL.Emit
import PicoRV.Decoder.DecoderCaptureStage

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-decoder-capture" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.Decoder.CaptureStage.naming)
