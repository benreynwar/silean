import Lake

open Lake DSL

package «silean» where

@[default_target]
lean_lib «Silean» where

@[default_target]
lean_lib «RV32I» where

@[default_target]
lean_lib «PicoRV» where

@[default_target]
lean_lib «SileanTests» where
  srcDir := "tests/silean/lean"
  roots := #[`SileanTests]

@[default_target]
lean_lib «PicoRVTests» where
  srcDir := "tests/picorv/lean"
  roots := #[`PicoRVTests]

lean_exe «emit-bit-register» where
  root := `Silean.Emitters.BitRegister

lean_exe «emit-structured-fifo» where
  root := `Silean.Emitters.StructuredFifo

lean_exe «emit-pointer-fifo» where
  root := `Silean.Emitters.PointerFifo

lean_exe «emit-serial-fifo» where
  root := `Silean.Emitters.SerialFifo

lean_exe «emit-bit-register-bank» where
  root := `Silean.Emitters.BitRegisterBank

lean_exe «emit-picorv-decoder-capture» where
  root := `PicoRV.Emitters.PicoRVDecoderCapture

lean_exe «emit-picorv-control» where
  root := `PicoRV.Emitters.PicoRVControl

lean_exe «emit-picorv-datapath» where
  root := `PicoRV.Emitters.PicoRVDatapath

lean_exe «emit-picorv-memory» where
  root := `PicoRV.Emitters.PicoRVMemory

lean_exe «emit-picorv» where
  root := `PicoRV.Emitters.PicoRV
