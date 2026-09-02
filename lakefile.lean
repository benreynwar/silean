import Lake

open Lake DSL

package «silean» where

@[default_target]
lean_lib «Silean» where

@[default_target]
lean_lib «SileanExamples» where
  roots := #[`SileanExamples]

lean_exe «emit-bit-register» where
  root := `Silean.Emitters.BitRegister

lean_exe «emit-structured-fifo» where
  root := `Silean.Emitters.StructuredFifo

lean_exe «emit-pointer-fifo» where
  root := `Silean.Emitters.PointerFifo

lean_exe «emit-bit-register-bank» where
  root := `Silean.Emitters.BitRegisterBank

lean_exe «emit-picorv-decoder-capture» where
  root := `Silean.Emitters.PicoRVDecoderCapture
